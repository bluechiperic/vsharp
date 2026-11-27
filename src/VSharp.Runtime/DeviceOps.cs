using System.Numerics;
using ILGPU;
using ILGPU.Algorithms;
using ILGPU.Runtime;

namespace VSharp.Runtime;

/// <summary>
/// Tensor builtins as called from functions with the 'device' effect. Float32 matmul and elementwise operations run on an
/// accelerator through ILGPU (CUDA when available, then OpenCL, then ILGPU's CPU accelerator); everything else, and all
/// Float64 work, uses <see cref="TensorOps"/>. Set VSHARP_DEVICE to cuda, opencl, cpu (ILGPU's CPU accelerator) or host
/// (no accelerator) to choose.
/// </summary>
public static class DeviceOps
{
    private sealed class Gpu : IDisposable
    {
        public required Context Context { get; init; }
        public required Accelerator Acc { get; init; }
        public required Action<Index2D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int, int> MatMul { get; init; }
        public required Action<Index1D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int> Binary { get; init; }
        public required Action<Index1D, ArrayView<float>, ArrayView<float>, int, float> Unary { get; init; }
        public required Action<Index1D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int> Bias { get; init; }
        public required Action<Index2D, ArrayView<float>, ArrayView<float>, int, int> Transpose { get; init; }

        public void Dispose()
        {
            Acc.Dispose();
            Context.Dispose();
        }
    }

    private static readonly Lazy<Gpu?> Instance = new(Create);

    /// <summary>The accelerator in use, or "host" when tensor operations run on the CPU without ILGPU.</summary>
    public static string DeviceName => Instance.Value is { } g ? $"{g.Acc.AcceleratorType} {g.Acc.Name}" : "host";

    private static Gpu? Create()
    {
        var want = (Environment.GetEnvironmentVariable("VSHARP_DEVICE") ?? "auto").ToLowerInvariant();
        if (want == "host") return null;
        var context = Context.Create(b => b.Default().EnableAlgorithms());
        var device = want switch
        {
            "cuda" => context.Devices.FirstOrDefault(d => d.AcceleratorType == AcceleratorType.Cuda),
            "opencl" => context.Devices.FirstOrDefault(d => d.AcceleratorType == AcceleratorType.OpenCL),
            "cpu" => context.Devices.FirstOrDefault(d => d.AcceleratorType == AcceleratorType.CPU),
            _ => context.GetPreferredDevice(preferCPU: false),
        };
        if (device == null)
        {
            context.Dispose();
            throw new InvalidOperationException($"VSHARP_DEVICE={want}: no such accelerator on this machine.");
        }
        var acc = device.CreateAccelerator(context);
        var gpu = new Gpu
        {
            Context = context,
            Acc = acc,
            MatMul = acc.LoadAutoGroupedStreamKernel<Index2D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int, int>(MatMulKernel),
            Binary = acc.LoadAutoGroupedStreamKernel<Index1D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int>(BinaryKernel),
            Unary = acc.LoadAutoGroupedStreamKernel<Index1D, ArrayView<float>, ArrayView<float>, int, float>(UnaryKernel),
            Bias = acc.LoadAutoGroupedStreamKernel<Index1D, ArrayView<float>, ArrayView<float>, ArrayView<float>, int>(BiasKernel),
            Transpose = acc.LoadAutoGroupedStreamKernel<Index2D, ArrayView<float>, ArrayView<float>, int, int>(TransposeKernel),
        };
        AppDomain.CurrentDomain.ProcessExit += (_, _) => gpu.Dispose();
        return gpu;
    }

    // ---------- kernels ----------

    private static void MatMulKernel(Index2D ix, ArrayView<float> a, ArrayView<float> b, ArrayView<float> c, int k, int n)
    {
        var s = 0f;
        for (var x = 0; x < k; x++) s += a[ix.X * k + x] * b[x * n + ix.Y];
        c[ix.X * n + ix.Y] = s;
    }

    private static void BinaryKernel(Index1D i, ArrayView<float> a, ArrayView<float> b, ArrayView<float> c, int op)
    {
        c[i] = op switch
        {
            0 => a[i] + b[i],
            1 => a[i] - b[i],
            2 => a[i] * b[i],
            3 => a[i] > 0f ? b[i] : 0f,
            4 => b[i] * (1f - a[i] * a[i]),
            _ => b[i] * a[i] * (1f - a[i]),
        };
    }

    private static void UnaryKernel(Index1D i, ArrayView<float> a, ArrayView<float> c, int op, float s)
    {
        var v = a[i];
        c[i] = op switch
        {
            0 => v > 0f ? v : 0f,
            1 => v * s,
            2 => 1f / (1f + MathF.Exp(-v)),
            _ => MathF.Tanh(v),
        };
    }

    private static void BiasKernel(Index1D i, ArrayView<float> x, ArrayView<float> b, ArrayView<float> c, int n) => c[i] = x[i] + b[i % n];

    private static void TransposeKernel(Index2D ix, ArrayView<float> a, ArrayView<float> c, int m, int n) => c[ix.Y * m + ix.X] = a[ix.X * n + ix.Y];

    // ---------- dispatch ----------

    /// <summary>
    /// Operations smaller than this many scalar operations stay on the host, where they are faster than a kernel launch
    /// and the accelerator is never initialized. VSHARP_DEVICE_MIN overrides it (0 sends everything to the accelerator).
    /// </summary>
    public static long MinWork { get; set; } = long.TryParse(Environment.GetEnvironmentVariable("VSHARP_DEVICE_MIN"), out var w) ? w : 1 << 16;

    private static bool OnDevice<T>(long work, out Gpu gpu) where T : unmanaged, IFloatingPointIeee754<T>
    {
        gpu = null!;
        if (typeof(T) != typeof(float) || work < MinWork || Instance.Value is not { } g) return false;
        gpu = g;
        return true;
    }

    private static float[] F(object data) => (float[])data;

    private static Tensor<T> Wrap<T>(float[] data, int[] shape) where T : unmanaged, IFloatingPointIeee754<T> => new((T[])(object)data, shape);

    private static Tensor<T> Run<T>(Gpu g, int[] shape, int length, Action<ArrayView<float>> launch) where T : unmanaged, IFloatingPointIeee754<T>
    {
        using var output = g.Acc.Allocate1D<float>(length);
        launch(output.View);
        g.Acc.Synchronize();
        return Wrap<T>(output.GetAsArray1D(), shape);
    }

    private static Tensor<T> Binary<T>(Tensor<T> a, Tensor<T> b, int op, string name, Func<Tensor<T>, Tensor<T>, Tensor<T>> host)
        where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (!OnDevice<T>(a.Data.Length, out var g)) return host(a, b);
        TensorOps.Require(a.Shape.AsSpan().SequenceEqual(b.Shape), name, a, b);
        using var da = g.Acc.Allocate1D(F(a.Data));
        using var db = g.Acc.Allocate1D(F(b.Data));
        return Run<T>(g, a.Shape, a.Data.Length, o => g.Binary(a.Data.Length, da.View, db.View, o, op));
    }

    private static Tensor<T> Unary<T>(Tensor<T> a, int op, float s, Func<Tensor<T>, Tensor<T>> host) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (!OnDevice<T>(a.Data.Length, out var g)) return host(a);
        using var da = g.Acc.Allocate1D(F(a.Data));
        return Run<T>(g, a.Shape, a.Data.Length, o => g.Unary(a.Data.Length, da.View, o, op, s));
    }

    public static Tensor<T> MatMul<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (!OnDevice<T>((long)a.Data.Length * (b.Shape.Length == 2 ? b.Shape[1] : 1), out var g)) return TensorOps.MatMul(a, b);
        TensorOps.Require(a.Shape.Length == 2 && b.Shape.Length == 2 && a.Shape[1] == b.Shape[0], "matmul", a, b);
        int m = a.Shape[0], k = a.Shape[1], n = b.Shape[1];
        using var da = g.Acc.Allocate1D(F(a.Data));
        using var db = g.Acc.Allocate1D(F(b.Data));
        return Run<T>(g, [m, n], m * n, o => g.MatMul(new Index2D(m, n), da.View, db.View, o, k, n));
    }

    public static Tensor<T> Add<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Binary(a, b, 0, "add", TensorOps.Add);
    public static Tensor<T> Sub<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Binary(a, b, 1, "sub", TensorOps.Sub);
    public static Tensor<T> Mul<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Binary(a, b, 2, "mul", TensorOps.Mul);
    public static Tensor<T> ReluGrad<T>(Tensor<T> x, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> => Binary(x, g, 3, "relu_grad", TensorOps.ReluGrad);
    public static Tensor<T> TanhGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> => Binary(y, g, 4, "tanh_grad", TensorOps.TanhGrad);
    public static Tensor<T> SigmoidGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> => Binary(y, g, 5, "sigmoid_grad", TensorOps.SigmoidGrad);
    public static Tensor<T> Relu<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Unary(x, 0, 0f, TensorOps.Relu);
    public static Tensor<T> Scale<T>(Tensor<T> x, double s) where T : unmanaged, IFloatingPointIeee754<T> => Unary(x, 1, (float)s, t => TensorOps.Scale(t, s));
    public static Tensor<T> Sigmoid<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Unary(x, 2, 0f, TensorOps.Sigmoid);
    public static Tensor<T> Tanh<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Unary(x, 3, 0f, TensorOps.Tanh);

    public static Tensor<T> AddBias<T>(Tensor<T> x, Tensor<T> bias) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (!OnDevice<T>(x.Data.Length, out var g)) return TensorOps.AddBias(x, bias);
        TensorOps.Require(x.Shape.Length == 2 && bias.Shape.Length == 1 && x.Shape[1] == bias.Shape[0], "add_bias", x, bias);
        using var dx = g.Acc.Allocate1D(F(x.Data));
        using var db = g.Acc.Allocate1D(F(bias.Data));
        return Run<T>(g, x.Shape, x.Data.Length, o => g.Bias(x.Data.Length, dx.View, db.View, o, bias.Shape[0]));
    }

    public static Tensor<T> Transpose<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (a.Shape.Length != 2 || !OnDevice<T>(a.Data.Length, out var g)) return TensorOps.Transpose(a);
        int m = a.Shape[0], n = a.Shape[1];
        using var da = g.Acc.Allocate1D(F(a.Data));
        return Run<T>(g, [n, m], m * n, o => g.Transpose(new Index2D(m, n), da.View, o, m, n));
    }

    public static Tensor<T> Softmax<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.Softmax(x);
    public static Tensor<T> SoftmaxGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.SoftmaxGrad(y, g);
    public static Tensor<T> SumRows<T>(Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.SumRows(g);
    public static Tensor<T> Reshape<T>(Tensor<T> a, int[] shape) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.Reshape(a, shape);
    public static Tensor<T> Full<T>(int[] shape, double v) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.Full<T>(shape, v);
    public static double Sum<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.Sum(a);
    public static Tensor<float> ToF32<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.ToF32(a);
    public static Tensor<double> ToF64<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T> => TensorOps.ToF64(a);
}
