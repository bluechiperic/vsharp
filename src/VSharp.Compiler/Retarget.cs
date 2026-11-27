using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
using System.Text;

namespace VSharp.Compiler;

/// <summary>
/// PersistedAssemblyBuilder references System.Private.CoreLib, which compilers never see: C# rejects a reference to an
/// assembly whose signatures use CoreLib types. System.Runtime forwards those types at run time and is the assembly
/// compilers reference, so the CoreLib reference is rewritten in place to name System.Runtime instead.
/// </summary>
internal static class Retarget
{
    public const string SystemRuntime = "System.Runtime";
    public static readonly byte[] SystemRuntimeToken = [0xb0, 0x3f, 0x5f, 0x7f, 0x11, 0xd5, 0x0a, 0x3a];

    private static readonly Lazy<HashSet<string>> Forwarded = new(() =>
    {
        var names = new HashSet<string>();
        var path = Path.Combine(RuntimeEnvironment.GetRuntimeDirectory(), SystemRuntime + ".dll");
        if (!File.Exists(path)) return names;
        using var pe = new PEReader(File.OpenRead(path));
        var md = pe.GetMetadataReader();
        foreach (var h in md.ExportedTypes)
        {
            var e = md.GetExportedType(h);
            if (e.Implementation.Kind == HandleKind.AssemblyReference) names.Add(Name(md, e.Namespace, e.Name));
        }
        return names;
    });

    /// <summary>
    /// Rewrites the image's System.Private.CoreLib reference to System.Runtime. The image must already contain the string
    /// "System.Runtime" and the System.Runtime public key token in its heaps. Leaves the image unchanged when any CoreLib
    /// type it uses is not forwarded by System.Runtime.
    /// </summary>
    public static void ToSystemRuntime(byte[] image)
    {
        int row, name, token;
        bool wideStrings, wideBlobs;
        using (var pe = new PEReader(ImmutableArray.Create(image)))
        {
            var md = pe.GetMetadataReader();
            var core = md.AssemblyReferences.FirstOrDefault(h => md.GetString(md.GetAssemblyReference(h).Name) == "System.Private.CoreLib");
            if (core.IsNil) return;
            foreach (var h in md.TypeReferences)
            {
                var t = md.GetTypeReference(h);
                if (t.ResolutionScope == (EntityHandle)core && !Forwarded.Value.Contains(Name(md, t.Namespace, t.Name))) return;
            }

            var start = pe.PEHeaders.MetadataStartOffset;
            name = Find(image, start + md.GetHeapMetadataOffset(HeapIndex.String), md.GetHeapSize(HeapIndex.String),
                        [.. Encoding.UTF8.GetBytes(SystemRuntime), 0]);
            token = Find(image, start + md.GetHeapMetadataOffset(HeapIndex.Blob), md.GetHeapSize(HeapIndex.Blob),
                         [(byte)SystemRuntimeToken.Length, .. SystemRuntimeToken]);
            if (name < 0 || token < 0) return;

            // The #~ stream header is 24 bytes plus a row count per present table; its HeapSizes byte is at offset 6.
            var present = Enumerable.Range(0, MetadataTokens.TableCount).Count(i => md.GetTableRowCount((TableIndex)i) > 0);
            var heapSizes = image[start + md.GetTableMetadataOffset(TableIndex.Module) - 24 - 4 * present + 6];
            wideStrings = (heapSizes & 0x01) != 0;
            wideBlobs = (heapSizes & 0x04) != 0;
            row = start + md.GetTableMetadataOffset(TableIndex.AssemblyRef)
                  + (MetadataTokens.GetRowNumber(core) - 1) * md.GetTableRowSize(TableIndex.AssemblyRef);
        }

        // AssemblyRef: four 2-byte version parts and 4-byte flags, then PublicKeyOrToken (blob) and Name (string).
        // The flags' PublicKey bit is cleared: the blob now holds a token, not a full key.
        image[row + 8] &= unchecked((byte)~0x01);
        var at = row + 12;
        Write(image, ref at, token, wideBlobs);
        Write(image, ref at, name, wideStrings);
    }

    private static string Name(MetadataReader md, StringHandle ns, StringHandle name) =>
        ns.IsNil || md.GetString(ns).Length == 0 ? md.GetString(name) : md.GetString(ns) + "." + md.GetString(name);

    /// <summary>The heap offset of <paramref name="pattern"/>, or -1.</summary>
    private static int Find(byte[] image, int heap, int size, byte[] pattern) => image.AsSpan(heap, size).IndexOf(pattern);

    private static void Write(byte[] image, ref int at, int value, bool wide)
    {
        image[at++] = (byte)value;
        image[at++] = (byte)(value >> 8);
        if (!wide) return;
        image[at++] = (byte)(value >> 16);
        image[at++] = (byte)(value >> 24);
    }
}
