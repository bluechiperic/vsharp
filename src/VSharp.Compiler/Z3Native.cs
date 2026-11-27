using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace VSharp.Compiler;

/// <summary>
/// Loads libz3 from beside the compiler or from <c>runtimes/&lt;rid&gt;/native</c>.
/// The official Microsoft.Z3 4.12.2 package ships an x64-only managed DLL and no Linux native,
/// so the build vendors an AnyCPU binding plus one native per RID. Returning zero lets the
/// default loader try the NuGet runtime asset as well.
/// </summary>
static class Z3Native
{
    [ModuleInitializer]
    internal static void Init() =>
        NativeLibrary.SetDllImportResolver(typeof(Microsoft.Z3.Context).Assembly, Resolve);

    private static IntPtr Resolve(string libraryName, Assembly assembly, DllImportSearchPath? searchPath)
    {
        if (!libraryName.Contains("z3", StringComparison.OrdinalIgnoreCase)) return IntPtr.Zero;
        var file = OperatingSystem.IsWindows() ? "libz3.dll"
            : OperatingSystem.IsMacOS() ? "libz3.dylib"
            : "libz3.so";
        foreach (var dir in ProbeDirectories(assembly))
        {
            var path = Path.Combine(dir, file);
            if (File.Exists(path) && NativeLibrary.TryLoad(path, out var handle)) return handle;
        }
        return IntPtr.Zero;
    }

    private static IEnumerable<string> ProbeDirectories(Assembly z3Assembly)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var root in Roots(z3Assembly))
        {
            if (seen.Add(root)) yield return root;
            foreach (var rid in Rids())
            {
                var native = Path.Combine(root, "runtimes", rid, "native");
                if (seen.Add(native)) yield return native;
            }
        }
    }

    private static IEnumerable<string> Roots(Assembly z3Assembly)
    {
        yield return AppContext.BaseDirectory;
        var z3Dir = Path.GetDirectoryName(z3Assembly.Location);
        if (!string.IsNullOrEmpty(z3Dir)) yield return z3Dir;
    }

    private static IEnumerable<string> Rids()
    {
        yield return RuntimeInformation.RuntimeIdentifier;
        var arch = RuntimeInformation.OSArchitecture switch
        {
            Architecture.X64 => "x64",
            Architecture.Arm64 => "arm64",
            Architecture.X86 => "x86",
            Architecture.Arm => "arm",
            _ => "x64",
        };
        if (OperatingSystem.IsWindows()) yield return "win-" + arch;
        else if (OperatingSystem.IsMacOS()) yield return "osx-" + arch;
        else if (OperatingSystem.IsLinux()) yield return "linux-" + arch;
    }
}
