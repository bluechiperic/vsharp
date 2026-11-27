using System.Globalization;
using System.Numerics;
using System.Reflection;
using System.Text;

namespace VSharp.Runtime;

/// <summary>Dense tensor with value semantics. Shapes are proved by the V# compiler; the runtime re-checks them only
/// as a defence against unverified (non-V#) callers.</summary>
public sealed class Tensor<T> where T : unmanaged, IFloatingPointIeee754<T>
{
    public T[] Data { get; }
    public int[] Shape { get; }

    public Tensor(T[] data, int[] shape)
    {
        var n = 1;
        foreach (var d in shape) n = checked(n * d);
        if (n != data.Length) throw new ArgumentException($"Tensor data length {data.Length} does not match shape [{string.Join(", ", shape)}].");
        Data = data;
        Shape = shape;
    }

    public override string ToString()
    {
        var sb = new StringBuilder();
        var pos = 0;
        Write(sb, 0, ref pos);
        return sb.ToString();
    }

    private void Write(StringBuilder sb, int axis, ref int pos)
    {
        if (axis == Shape.Length)
        {
            sb.Append(double.CreateTruncating(Data[pos++]).ToString("0.####", CultureInfo.InvariantCulture));
            return;
        }
        sb.Append('[');
        for (var i = 0; i < Shape[axis]; i++)
        {
            if (i > 0) sb.Append(", ");
            Write(sb, axis + 1, ref pos);
        }
        sb.Append(']');
    }
}

/// <summary>Deterministic CPU implementations of the tensor builtins. Pure V# functions always use these.</summary>
public static class TensorOps
{
    public static Tensor<T> MatMul<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T>
    {
        Require(a.Shape.Length == 2 && b.Shape.Length == 2 && a.Shape[1] == b.Shape[0], "matmul", a, b);
        int m = a.Shape[0], k = a.Shape[1], n = b.Shape[1];
        var r = new T[m * n];
        for (var i = 0; i < m; i++)
            for (var x = 0; x < k; x++)
            {
                var av = a.Data[i * k + x];
                for (var j = 0; j < n; j++) r[i * n + j] += av * b.Data[x * n + j];
            }
        return new Tensor<T>(r, [m, n]);
    }

    public static Tensor<T> Add<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Zip(a, b, "add", (x, y) => x + y);
    public static Tensor<T> Sub<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Zip(a, b, "sub", (x, y) => x - y);
    public static Tensor<T> Mul<T>(Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T> => Zip(a, b, "mul", (x, y) => x * y);

    public static Tensor<T> Scale<T>(Tensor<T> a, double s) where T : unmanaged, IFloatingPointIeee754<T>
    {
        var f = T.CreateTruncating(s);
        return Map(a, x => x * f);
    }

    public static Tensor<T> AddBias<T>(Tensor<T> x, Tensor<T> bias) where T : unmanaged, IFloatingPointIeee754<T>
    {
        Require(x.Shape.Length == 2 && bias.Shape.Length == 1 && x.Shape[1] == bias.Shape[0], "add_bias", x, bias);
        var n = bias.Shape[0];
        var r = new T[x.Data.Length];
        for (var i = 0; i < r.Length; i++) r[i] = x.Data[i] + bias.Data[i % n];
        return new Tensor<T>(r, x.Shape);
    }

    public static Tensor<T> Relu<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Map(x, v => T.Max(T.Zero, v));
    public static Tensor<T> Tanh<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Map(x, T.Tanh);
    public static Tensor<T> Sigmoid<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T> => Map(x, v => T.One / (T.One + T.Exp(-v)));

    public static Tensor<T> Softmax<T>(Tensor<T> x) where T : unmanaged, IFloatingPointIeee754<T>
    {
        int m = x.Shape[0], n = x.Shape[1];
        var r = new T[x.Data.Length];
        for (var i = 0; i < m; i++)
        {
            var max = x.Data[i * n];
            for (var j = 1; j < n; j++) max = T.Max(max, x.Data[i * n + j]);
            var total = T.Zero;
            for (var j = 0; j < n; j++) total += r[i * n + j] = T.Exp(x.Data[i * n + j] - max);
            for (var j = 0; j < n; j++) r[i * n + j] /= total;
        }
        return new Tensor<T>(r, x.Shape);
    }

    public static Tensor<T> Transpose<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (a.Shape.Length != 2) throw new ArgumentException("transpose requires a rank-2 tensor.");
        int m = a.Shape[0], n = a.Shape[1];
        var r = new T[a.Data.Length];
        for (var i = 0; i < m; i++)
            for (var j = 0; j < n; j++) r[j * m + i] = a.Data[i * n + j];
        return new Tensor<T>(r, [n, m]);
    }

    public static Tensor<T> Reshape<T>(Tensor<T> a, int[] shape) where T : unmanaged, IFloatingPointIeee754<T> => new((T[])a.Data.Clone(), shape);

    public static Tensor<T> Full<T>(int[] shape, double v) where T : unmanaged, IFloatingPointIeee754<T>
    {
        var n = 1;
        foreach (var d in shape) n = checked(n * d);
        var r = new T[n];
        Array.Fill(r, T.CreateTruncating(v));
        return new Tensor<T>(r, shape);
    }

    public static double Sum<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T>
    {
        var s = 0.0;
        foreach (var v in a.Data) s += double.CreateTruncating(v);
        return s;
    }

    public static Tensor<float> ToF32<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T> =>
        new(a.Data.Select(float.CreateTruncating).ToArray(), a.Shape);

    public static Tensor<double> ToF64<T>(Tensor<T> a) where T : unmanaged, IFloatingPointIeee754<T> =>
        new(a.Data.Select(double.CreateTruncating).ToArray(), a.Shape);

    public static Tensor<T> ReluGrad<T>(Tensor<T> x, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> =>
        Zip(x, g, "relu_grad", (a, b) => a > T.Zero ? b : T.Zero);

    public static Tensor<T> TanhGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> =>
        Zip(y, g, "tanh_grad", (a, b) => b * (T.One - a * a));

    public static Tensor<T> SigmoidGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T> =>
        Zip(y, g, "sigmoid_grad", (a, b) => b * a * (T.One - a));

    public static Tensor<T> SoftmaxGrad<T>(Tensor<T> y, Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T>
    {
        Require(y.Shape.AsSpan().SequenceEqual(g.Shape) && y.Shape.Length == 2, "softmax_grad", y, g);
        int m = y.Shape[0], n = y.Shape[1];
        var r = new T[y.Data.Length];
        for (var i = 0; i < m; i++)
        {
            var dot = T.Zero;
            for (var j = 0; j < n; j++) dot += y.Data[i * n + j] * g.Data[i * n + j];
            for (var j = 0; j < n; j++) r[i * n + j] = y.Data[i * n + j] * (g.Data[i * n + j] - dot);
        }
        return new Tensor<T>(r, y.Shape);
    }

    public static Tensor<T> SumRows<T>(Tensor<T> g) where T : unmanaged, IFloatingPointIeee754<T>
    {
        int m = g.Shape[0], n = g.Shape[1];
        var r = new T[n];
        for (var i = 0; i < m; i++)
            for (var j = 0; j < n; j++) r[j] += g.Data[i * n + j];
        return new Tensor<T>(r, [n]);
    }

    private static Tensor<T> Map<T>(Tensor<T> a, Func<T, T> f) where T : unmanaged, IFloatingPointIeee754<T>
    {
        var r = new T[a.Data.Length];
        for (var i = 0; i < r.Length; i++) r[i] = f(a.Data[i]);
        return new Tensor<T>(r, a.Shape);
    }

    private static Tensor<T> Zip<T>(Tensor<T> a, Tensor<T> b, string op, Func<T, T, T> f) where T : unmanaged, IFloatingPointIeee754<T>
    {
        Require(a.Shape.AsSpan().SequenceEqual(b.Shape), op, a, b);
        var r = new T[a.Data.Length];
        for (var i = 0; i < r.Length; i++) r[i] = f(a.Data[i], b.Data[i]);
        return new Tensor<T>(r, a.Shape);
    }

    internal static void Require<T>(bool ok, string op, Tensor<T> a, Tensor<T> b) where T : unmanaged, IFloatingPointIeee754<T>
    {
        if (!ok) throw new ArgumentException($"{op}: incompatible shapes [{string.Join(", ", a.Shape)}] and [{string.Join(", ", b.Shape)}].");
    }
}

/// <summary>Helpers the compiler calls for value-semantic arrays, printing and entry checks.</summary>
public static class Rt
{
    public static T[] Update<T>(T[] a, long index, T value)
    {
        var r = (T[])a.Clone();
        r[index] = value;
        return r;
    }

    public static T[] Fill<T>(long length, T value)
    {
        var r = new T[length];
        Array.Fill(r, value);
        return r;
    }

    public static void Print<T>(T value) => Console.WriteLine(Format(value));

    /// <summary>The printed form of a value. Strings print as they are at the top level and quoted inside other values.</summary>
    public static string Format(object? v) => Format(v, nested: false);

    private static string Format(object? v, bool nested) => v switch
    {
        null => "()",
        string s => nested ? "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"" : s,
        bool b => b ? "true" : "false",
        long l => l.ToString(CultureInfo.InvariantCulture),
        int i => i.ToString(CultureInfo.InvariantCulture),
        double d => d.ToString("R", CultureInfo.InvariantCulture),
        decimal m => m.ToString(CultureInfo.InvariantCulture),
        DateOnly d => Str(d),
        Array a => "[" + string.Join(", ", a.Cast<object?>().Select(x => Format(x, true))) + "]",
        IVSharpCollection c => c.Format(x => Format(x, true)),
        _ when v.GetType().IsGenericType && v.GetType().GetGenericTypeDefinition() == typeof(Tensor<>) => v.ToString()!,
        _ => FormatValue(v),
    };

    private static readonly System.Collections.Concurrent.ConcurrentDictionary<Type, FieldInfo[]> FieldCache = new();

    /// <summary>The fields of a V# record, union case or exception, in declaration order (not those of System.Exception).</summary>
    private static FieldInfo[] FieldsOf(Type t) => FieldCache.GetOrAdd(t, x =>
        x.GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.DeclaredOnly).OrderBy(f => f.MetadataToken).ToArray());

    private static string FormatValue(object v)
    {
        var t = v.GetType();
        var name = t.Name.Split('`')[0];
        var fields = FieldsOf(t);
        return fields.Length == 0 ? name : $"{name}({string.Join(", ", fields.Select(f => $"{f.Name.TrimEnd('$')}: {Format(f.GetValue(v), true)}"))})";
    }

    /// <summary>Structural equality of V# records and union cases (their Equals override).</summary>
    public static bool StructEquals(object self, object? other)
    {
        if (ReferenceEquals(self, other)) return true;
        if (other == null || other.GetType() != self.GetType()) return false;
        foreach (var f in FieldsOf(self.GetType()))
            if (!Equals(f.GetValue(self), f.GetValue(other))) return false;
        return true;
    }

    /// <summary>A hash consistent with <see cref="StructEquals"/> (their GetHashCode override).</summary>
    public static int StructHash(object self)
    {
        var h = new HashCode();
        h.Add(self.GetType());
        foreach (var f in FieldsOf(self.GetType())) h.Add(f.GetValue(self));
        return h.ToHashCode();
    }

    // ---------- strings ----------

    public static string Str(long v) => v.ToString(CultureInfo.InvariantCulture);
    public static string Str(int v) => v.ToString(CultureInfo.InvariantCulture);
    public static string Str(bool v) => v ? "true" : "false";
    public static string Str(decimal v) => v.ToString(CultureInfo.InvariantCulture);
    public static string Str(DateOnly v) => v.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture);
    public static string Str(string v) => v;

    public static long StrLen(string s) => s.Length;
    public static string Substring(string s, long start, long length) => s.Substring(checked((int)start), checked((int)length));
    public static long IndexOf(string s, string t) => s.IndexOf(t, StringComparison.Ordinal);
    public static bool Contains(string s, string t) => s.Contains(t, StringComparison.Ordinal);
    public static bool StartsWith(string s, string t) => s.StartsWith(t, StringComparison.Ordinal);
    public static bool EndsWith(string s, string t) => s.EndsWith(t, StringComparison.Ordinal);
    public static string Trim(string s) => s.Trim();
    public static string Upper(string s) => s.ToUpperInvariant();
    public static string Lower(string s) => s.ToLowerInvariant();
    public static string[] Split(string s, string separator) => s.Split(separator);
    public static string Join(string[] parts, string separator) => string.Join(separator, parts);
    public static bool EqIgnoreCase(string a, string b) => string.Equals(a, b, StringComparison.OrdinalIgnoreCase);
    public static bool IsBlank(string s) => string.IsNullOrWhiteSpace(s);
    public static bool StrEq(string a, string b) => string.Equals(a, b, StringComparison.Ordinal);

    public static bool TryParseInt(string s, out long value) => long.TryParse(s, NumberStyles.Integer, CultureInfo.InvariantCulture, out value);
    public static bool TryParseDecimal(string s, out decimal value) => decimal.TryParse(s, NumberStyles.Number, CultureInfo.InvariantCulture, out value);
    public static bool TryParseDate(string s, string format, out DateOnly value) =>
        DateOnly.TryParseExact(s, format, CultureInfo.InvariantCulture, DateTimeStyles.None, out value);

    /// <summary>A time of day in minutes since midnight, parsed with the first matching format.</summary>
    public static bool TryParseTime(string s, string[] formats, out long minutes)
    {
        var ok = DateTime.TryParseExact(s, formats, CultureInfo.InvariantCulture, DateTimeStyles.None, out var t);
        minutes = ok ? t.Hour * 60 + t.Minute : 0;
        return ok;
    }

    // ---------- numbers and dates ----------

    public static decimal Round(decimal d, long places) => Math.Round(d, checked((int)places), MidpointRounding.AwayFromZero);
    public static int DecCompare(decimal a, decimal b) => decimal.Compare(a, b);
    public static bool HasBit(long mask, long bit) => ((mask >> checked((int)bit)) & 1) == 1;

    public static DateOnly MakeDate(long year, long month, long day) => new(checked((int)year), checked((int)month), checked((int)day));
    public static bool IsValidDate(long year, long month, long day) =>
        year is >= 1 and <= 9999 && month is >= 1 and <= 12 && day >= 1 && day <= DateTime.DaysInMonth((int)year, (int)month);
    public static DateOnly AddDays(DateOnly d, long days) => d.AddDays(checked((int)days));
    public static long DaysBetween(DateOnly a, DateOnly b) => b.DayNumber - a.DayNumber;
    public static long DayOfWeek(DateOnly d) => (long)d.DayOfWeek;
    public static long Year(DateOnly d) => d.Year;
    public static long Month(DateOnly d) => d.Month;
    public static long Day(DateOnly d) => d.Day;
    public static int DayNumber(DateOnly d) => d.DayNumber;

    // ---------- arrays ----------

    public static T[] Append<T>(T[] a, T x)
    {
        var r = new T[a.Length + 1];
        a.CopyTo(r, 0);
        r[a.Length] = x;
        return r;
    }

    public static T[] Concat<T>(T[] a, T[] b)
    {
        var r = new T[a.Length + b.Length];
        a.CopyTo(r, 0);
        b.CopyTo(r, a.Length);
        return r;
    }

    public static T[] Filter<T>(T[] items, bool[] keep)
    {
        var r = new List<T>();
        for (var i = 0; i < items.Length; i++) if (keep[i]) r.Add(items[i]);
        return [.. r];
    }

    /// <summary>Strings order by ordinal (code unit) comparison; everything else by its natural order.</summary>
    private static IComparer<K> Order<K>() => typeof(K) == typeof(string) ? (IComparer<K>)StringComparer.Ordinal : Comparer<K>.Default;

    /// <summary>A stable sort of <paramref name="items"/> by the precomputed <paramref name="keys"/>.</summary>
    public static T[] SortBy<T, K>(T[] items, K[] keys, bool descending)
    {
        var idx = Enumerable.Range(0, items.Length);
        var sorted = descending ? idx.OrderByDescending(i => keys[i], Order<K>()) : idx.OrderBy(i => keys[i], Order<K>());
        return sorted.Select(i => items[i]).ToArray();
    }

    /// <summary>The index of the first smallest (or largest) key, or -1 for no keys.</summary>
    public static int BestIndex<K>(K[] keys, bool largest)
    {
        var cmp = Order<K>();
        var best = -1;
        for (var i = 0; i < keys.Length; i++)
        {
            if (best < 0) { best = i; continue; }
            var c = cmp.Compare(keys[i], keys[best]);
            if (largest ? c > 0 : c < 0) best = i;
        }
        return best;
    }

    public static Map<K, T[]> GroupBy<T, K>(T[] items, K[] keys) where K : notnull
    {
        var order = new List<K>();
        var groups = new Dictionary<K, List<T>>();
        for (var i = 0; i < items.Length; i++)
        {
            if (!groups.TryGetValue(keys[i], out var g)) { groups[keys[i]] = g = []; order.Add(keys[i]); }
            g.Add(items[i]);
        }
        var m = Map<K, T[]>.Empty();
        foreach (var k in order) m = m.Put(k, [.. groups[k]]);
        return m;
    }

    public static Map<K, V> ToMap<K, V>(K[] keys, V[] values) where K : notnull
    {
        var m = Map<K, V>.Empty();
        for (var i = 0; i < keys.Length; i++) m = m.Put(keys[i], values[i]);
        return m;
    }

    public static ContractViolationException Violation(string function, string clause) =>
        new($"{function}: precondition violated by the caller: {clause}");
}

public sealed class ContractViolationException(string message) : Exception(message);

internal interface IVSharpCollection
{
    string Format(Func<object?, string> item);
}

/// <summary>
/// V#'s Map[K, V]: immutable, with keys in insertion order (replacing a value keeps its key's position). Every
/// operation returns a new map. Readable from C# as an <see cref="IReadOnlyDictionary{K, V}"/>.
/// </summary>
public sealed class Map<K, V> : IReadOnlyDictionary<K, V>, IVSharpCollection where K : notnull
{
    private readonly K[] _keys;
    private readonly Dictionary<K, V> _values;

    private Map(K[] keys, Dictionary<K, V> values) { _keys = keys; _values = values; }

    public static Map<K, V> Empty() => new([], new Dictionary<K, V>());

    public static Map<K, V> From(IEnumerable<KeyValuePair<K, V>> pairs)
    {
        var m = Empty();
        foreach (var (k, v) in pairs) m = m.Put(k, v);
        return m;
    }

    public Map<K, V> Put(K key, V value)
    {
        var values = new Dictionary<K, V>(_values) { [key] = value };
        return new(_values.ContainsKey(key) ? _keys : [.. _keys, key], values);
    }

    public Map<K, V> Remove(K key)
    {
        if (!_values.ContainsKey(key)) return this;
        var values = new Dictionary<K, V>(_values);
        values.Remove(key);
        return new(_keys.Where(k => !EqualityComparer<K>.Default.Equals(k, key)).ToArray(), values);
    }

    public bool Has(K key) => _values.ContainsKey(key);
    public V GetValue(K key) => _values[key];
    public V GetOr(K key, V fallback) => _values.TryGetValue(key, out var v) ? v : fallback;
    public long Size() => _keys.Length;
    public K[] KeyArray() => [.. _keys];
    public V[] ValueArray() => _keys.Select(k => _values[k]).ToArray();

    public V this[K key] => _values[key];
    public IEnumerable<K> Keys => _keys;
    public IEnumerable<V> Values => _keys.Select(k => _values[k]);
    public int Count => _keys.Length;
    public bool ContainsKey(K key) => _values.ContainsKey(key);
    public bool TryGetValue(K key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out V value) => _values.TryGetValue(key, out value);
    public IEnumerator<KeyValuePair<K, V>> GetEnumerator() => _keys.Select(k => new KeyValuePair<K, V>(k, _values[k])).GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();

    string IVSharpCollection.Format(Func<object?, string> item) =>
        "{" + string.Join(", ", _keys.Select(k => $"{item(k)}: {item(_values[k])}")) + "}";

    public override string ToString() => Rt.Format(this);
}

/// <summary>V#'s Set[T]: immutable, with items in insertion order. Readable from C# as an <see cref="IReadOnlyCollection{T}"/>.</summary>
public sealed class Set<T> : IReadOnlyCollection<T>, IVSharpCollection where T : notnull
{
    private readonly T[] _items;
    private readonly HashSet<T> _members;

    private Set(T[] items, HashSet<T> members) { _items = items; _members = members; }

    public static Set<T> Empty() => new([], new HashSet<T>());

    public static Set<T> Of(T[] items)
    {
        var order = new List<T>();
        var members = new HashSet<T>();
        foreach (var x in items) if (members.Add(x)) order.Add(x);
        return new([.. order], members);
    }

    public Set<T> Add(T item) => _members.Contains(item) ? this : new([.. _items, item], [.. _members, item]);
    public bool Has(T item) => _members.Contains(item);
    public long Size() => _items.Length;
    public T[] ItemArray() => [.. _items];

    public int Count => _items.Length;
    public IEnumerator<T> GetEnumerator() => ((IEnumerable<T>)_items).GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();

    string IVSharpCollection.Format(Func<object?, string> item) => "{" + string.Join(", ", _items.Select(x => item(x))) + "}";

    public override string ToString() => Rt.Format(this);
}

/// <summary>A contract clause carried in metadata so other tools and languages can read it.
/// Kind is "requires", "ensures", or "requires-unchecked" for a precondition that cannot be checked at run time.</summary>
[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
public sealed class ContractAttribute(string kind, string text) : Attribute
{
    public string Kind { get; } = kind;
    public string Text { get; } = text;
}

/// <summary>Marks a module whose proof obligations were all discharged at compile time.</summary>
[AttributeUsage(AttributeTargets.Class)]
public sealed class VerifiedAttribute(string tool) : Attribute
{
    public string Tool { get; } = tool;
}
