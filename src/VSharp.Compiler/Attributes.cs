using System.Globalization;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
using System.Runtime.Loader;

namespace VSharp.Compiler;

/// <summary>
/// Resolves '@Name(args)' to a .NET attribute type and binds its arguments. Types are found in the assemblies already
/// loaded, the .NET runtime directory and the assemblies given with '--reference'.
/// </summary>
public sealed class AttributeBinder(DiagnosticBag diags, IReadOnlyList<string> uses, IReadOnlyList<string> references)
{
    private static readonly Dictionary<string, string> Index = new(StringComparer.Ordinal);
    private static readonly HashSet<string> Indexed = new(StringComparer.OrdinalIgnoreCase);
    private static readonly HashSet<string> ProbeDirs = new(StringComparer.OrdinalIgnoreCase);
    private static bool _hooked;

    /// <summary>Resolves and validates the attributes on one declaration.</summary>
    public void Bind(List<Attr> attrs, AttrTarget target, string what)
    {
        var seen = new HashSet<Type>();
        foreach (var a in attrs)
        {
            var type = Resolve(a);
            if (type == null) continue;
            var usage = type.GetCustomAttribute<AttributeUsageAttribute>(inherit: true) ?? new AttributeUsageAttribute(AttributeTargets.All);
            var flag = target switch
            {
                AttrTarget.Class => AttributeTargets.Class,
                AttrTarget.Interface => AttributeTargets.Interface,
                AttrTarget.Property => AttributeTargets.Property,
                AttrTarget.Method => AttributeTargets.Method,
                _ => AttributeTargets.Parameter,
            };
            if ((usage.ValidOn & flag) == 0)
                diags.Error("TN2026", a.Span, $"attribute '{type.FullName}' cannot be applied to {what}",
                    $"It applies to: {usage.ValidOn}. In the assembly, a field is a property, a function or method is a method, a record or class is a class.");
            if (!seen.Add(type) && !usage.AllowMultiple)
                diags.Error("TN2026", a.Span, $"attribute '{type.FullName}' can be applied only once");
            BindArgs(a, type);
        }
    }

    private Type? Resolve(Attr a)
    {
        var candidates = new List<string> { a.Name };
        candidates.AddRange(uses.Prepend("System").Distinct().Select(u => $"{u}.{a.Name}"));
        var found = candidates
            .SelectMany(c => new[] { c + "Attribute", c })
            .Select(Find)
            .OfType<Type>()
            .Where(t => typeof(Attribute).IsAssignableFrom(t))
            .Distinct()
            .ToList();
        if (found.Count == 0)
        {
            var notAttribute = candidates.Select(Find).OfType<Type>().FirstOrDefault();
            diags.Error("TN2026", a.Span, notAttribute != null ? $"'{notAttribute.FullName}' is not an attribute" : $"unknown attribute '{a.Name}'",
                notAttribute != null ? null : "Write the attribute's full .NET name, or add 'use Namespace' to the module. Assemblies outside the .NET runtime need '--reference <dll>'.");
            return null;
        }
        if (found.Count > 1)
        {
            diags.Error("TN2026", a.Span, $"attribute '{a.Name}' is ambiguous: {string.Join(", ", found.Select(t => t.FullName))}", "Write its full name.");
            return null;
        }
        if (found[0].IsAbstract)
        {
            diags.Error("TN2026", a.Span, $"attribute '{found[0].FullName}' is abstract");
            return null;
        }
        return found[0];
    }

    private void BindArgs(Attr a, Type type)
    {
        var positional = a.Args.Where((_, i) => a.ArgNames[i] == null).ToList();
        if (a.ArgNames.SkipWhile(n => n == null).Any(n => n == null))
        {
            diags.Error("TN2026", a.Span, "positional arguments of an attribute come before named ones");
            return;
        }
        ConstructorInfo? ctor = null;
        object?[]? values = null;
        foreach (var c in type.GetConstructors().OrderBy(c => c.MetadataToken))
        {
            var ps = c.GetParameters();
            if (ps.Length != positional.Count) continue;
            var converted = new object?[ps.Length];
            var ok = true;
            for (var i = 0; i < ps.Length && ok; i++) ok = TryConvert(positional[i], ps[i].ParameterType, out converted[i]);
            if (!ok) continue;
            (ctor, values) = (c, converted);
            break;
        }
        if (ctor == null)
        {
            var sigs = type.GetConstructors().Select(c => $"({string.Join(", ", c.GetParameters().Select(p => $"{p.ParameterType.Name} {p.Name}"))})");
            diags.Error("TN2026", a.Span, $"no constructor of '{type.FullName}' takes these arguments",
                $"Its constructors are: {string.Join(", ", sigs)}. Arguments are literals, enum members (Enum.Member) and arrays of those.");
            return;
        }
        a.Ctor = ctor;
        a.CtorArgs = values!;
        for (var i = 0; i < a.Args.Count; i++)
        {
            if (a.ArgNames[i] is not { } name) continue;
            MemberInfo? member = type.GetProperty(name, BindingFlags.Public | BindingFlags.Instance) is { CanWrite: true, SetMethod.IsPublic: true } p ? p
                : type.GetField(name, BindingFlags.Public | BindingFlags.Instance) is { IsInitOnly: false, IsLiteral: false } f ? f : null;
            if (member == null)
            {
                diags.Error("TN2026", a.Args[i].Span, $"'{type.FullName}' has no settable property or field '{name}'");
                continue;
            }
            var mt = member is PropertyInfo pi ? pi.PropertyType : ((FieldInfo)member).FieldType;
            if (!TryConvert(a.Args[i], mt, out var v))
            {
                diags.Error("TN2026", a.Args[i].Span, $"'{name}' of '{type.FullName}' needs a {mt.Name} value");
                continue;
            }
            a.Named.Add((member, v));
        }
    }

    /// <summary>Converts a literal, an enum member name or an array of those to a value of the .NET type <paramref name="t"/>.</summary>
    private static bool TryConvert(Expr e, Type t, out object? value)
    {
        value = null;
        if (t == typeof(object) && e is IntLit or StrLit or BoolLit or FloatLit) t = e switch { IntLit => typeof(int), StrLit => typeof(string), BoolLit => typeof(bool), _ => typeof(double) };
        switch (e)
        {
            case StrLit s when t == typeof(string):
                value = s.Value;
                return true;
            case BoolLit b when t == typeof(bool):
                value = b.Value;
                return true;
            case IntLit or Unary { Op: "-", Operand: IntLit } when !t.IsEnum && Type.GetTypeCode(t) is >= TypeCode.SByte and <= TypeCode.Double:
            {
                var n = e is IntLit i ? i.Value : -((IntLit)((Unary)e).Operand).Value;
                try
                {
                    value = Convert.ChangeType(n, t, CultureInfo.InvariantCulture);
                    return true;
                }
                catch (OverflowException)
                {
                    return false;
                }
            }
            case FloatLit or Unary { Op: "-", Operand: FloatLit } when t == typeof(double) || t == typeof(float):
            {
                var d = e is FloatLit f ? f.Value : -((FloatLit)((Unary)e).Operand).Value;
                value = t == typeof(float) ? (float)d : d;
                return true;
            }
            case Var or FieldAccess when t.IsEnum:
            {
                var path = DottedText(e);
                if (path == null) return false;
                var dot = path.LastIndexOf('.');
                var (prefix, member) = dot < 0 ? ("", path) : (path[..dot], path[(dot + 1)..]);
                if (prefix.Length > 0 && prefix != t.Name && prefix != t.FullName) return false;
                if (!Enum.GetNames(t).Contains(member)) return false;
                value = Enum.Parse(t, member);
                return true;
            }
            case ArrayLit arr when t.IsArray:
            {
                var et = t.GetElementType()!;
                var items = Array.CreateInstance(et, arr.Elems.Count);
                for (var k = 0; k < arr.Elems.Count; k++)
                {
                    if (!TryConvert(arr.Elems[k], et, out var item)) return false;
                    items.SetValue(item, k);
                }
                value = items;
                return true;
            }
            default:
                return false;
        }
    }

    private static string? DottedText(Expr e) => e switch
    {
        Var v => v.Name,
        FieldAccess f when DottedText(f.Target) is { } t => $"{t}.{f.Field}",
        _ => null,
    };

    // ---------- finding types ----------

    private Type? Find(string fullName)
    {
        foreach (var asm in AppDomain.CurrentDomain.GetAssemblies())
            if (!asm.IsDynamic && asm.GetType(fullName) is { } t) return t;
        lock (Index)
        {
            IndexDirectory(RuntimeEnvironment.GetRuntimeDirectory(), framework: true);
            foreach (var r in references) IndexFile(Path.GetFullPath(r), framework: false);
            if (!Index.TryGetValue(fullName, out var path)) return null;
            return Load(path).GetType(fullName);
        }
    }

    private static void IndexDirectory(string dir, bool framework)
    {
        if (!Indexed.Add(dir)) return;
        foreach (var file in Directory.EnumerateFiles(dir, "*.dll")) IndexFile(file, framework);
    }

    private static void IndexFile(string file, bool framework)
    {
        if (!Indexed.Add(file)) return;
        if (!framework) ProbeDirs.Add(Path.GetDirectoryName(file)!);
        try
        {
            using var pe = new PEReader(File.OpenRead(file));
            if (!pe.HasMetadata) return;
            var md = pe.GetMetadataReader();
            if (!md.IsAssembly) return;
            foreach (var h in md.TypeDefinitions)
            {
                var td = md.GetTypeDefinition(h);
                if ((td.Attributes & TypeAttributes.VisibilityMask) != TypeAttributes.Public) continue;
                var ns = md.GetString(td.Namespace);
                var name = md.GetString(td.Name);
                Index.TryAdd(ns.Length == 0 ? name : $"{ns}.{name}", file);
            }
        }
        catch (BadImageFormatException)
        {
        }
    }

    private static Assembly Load(string path)
    {
        if (!_hooked)
        {
            _hooked = true;
            AssemblyLoadContext.Default.Resolving += (ctx, name) =>
            {
                foreach (var dir in ProbeDirs)
                {
                    var candidate = Path.Combine(dir, name.Name + ".dll");
                    if (File.Exists(candidate)) return ctx.LoadFromAssemblyPath(candidate);
                }
                return null;
            };
        }
        var an = AssemblyName.GetAssemblyName(path);
        try
        {
            return Assembly.Load(an);
        }
        catch (FileNotFoundException)
        {
            return Assembly.LoadFrom(path);
        }
    }
}
