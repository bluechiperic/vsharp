using System.Reflection;
using System.Reflection.Emit;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using VSharp.Runtime;

namespace VSharp.Compiler;

/// <summary>
/// Lowers a checked module to IL. Records become sealed classes; unions become an abstract class with one sealed subclass
/// per case; generic types and functions become CLR generics. Functions become static methods of a static class named
/// after the module. A function with checkable preconditions gets a public wrapper that checks them and a private
/// implementation that V# code calls directly, because V# callers have already proved them.
/// </summary>
public sealed class Emitter(ModuleDecl module, IReadOnlyList<string> sources, bool entryChecks = true)
{
    public Emitter(ModuleDecl module, string source, bool entryChecks = true) : this(module, [source], entryChecks) { }

    private sealed record CaseInfo(TypeBuilder Type, ConstructorBuilder Ctor, FieldBuilder[] Fields);

    private static readonly Dictionary<string, string> OpNames = new()
    {
        ["matmul"] = "MatMul", ["add"] = "Add", ["sub"] = "Sub", ["mul"] = "Mul", ["scale"] = "Scale", ["add_bias"] = "AddBias",
        ["relu"] = "Relu", ["tanh"] = "Tanh", ["sigmoid"] = "Sigmoid", ["softmax"] = "Softmax", ["transpose"] = "Transpose",
        ["reshape"] = "Reshape", ["full"] = "Full", ["sum"] = "Sum", ["to_f32"] = "ToF32", ["to_f64"] = "ToF64",
        ["relu_grad"] = "ReluGrad", ["tanh_grad"] = "TanhGrad", ["sigmoid_grad"] = "SigmoidGrad", ["softmax_grad"] = "SoftmaxGrad",
        ["sum_rows"] = "SumRows",
    };

    private ModuleBuilder _mb = null!;
    private readonly Dictionary<TypeDecl, TypeBuilder> _types = [];
    private readonly Dictionary<TypeDecl, ConstructorBuilder> _baseCtors = [];
    private readonly Dictionary<CaseDecl, CaseInfo> _cases = [];
    private readonly Dictionary<TypeDecl, CaseInfo> _records = [];
    private readonly Dictionary<FnDecl, MethodBuilder> _impls = [];
    private readonly Dictionary<FnDecl, MethodBuilder> _abstracts = [];
    private readonly List<(TypeDecl Class, CaseInfo Info)> _checkedCtors = [];
    private readonly List<TypeBuilder> _machines = [];
    private readonly Dictionary<ExceptionDecl, CaseInfo> _exceptions = [];

    /// <summary>
    /// A try block being emitted in an async function. A resumption inside it re-enters at its first instruction,
    /// which branches to <see cref="Dispatch"/>: there, the state picks the resume point (or the nested try's entry).
    /// </summary>
    private sealed class TryCtx(Label entry, Label body, Label dispatch)
    {
        public Label Entry { get; } = entry;
        public Label Body { get; } = body;
        public Label Dispatch { get; } = dispatch;
        public List<(int State, Label Target)> Inner { get; } = [];
    }

    private readonly List<TryCtx> _tryStack = [];
    /// <summary>How many try blocks enclose the current instruction; leaving one needs 'leave', not 'br' or 'ret'.</summary>
    private int _tryDepth;
    /// <summary>A label outside every try block that returns <see cref="_retLocal"/> (or nothing), for a 'return' inside one.</summary>
    private Label? _exit;
    private LocalBuilder? _retLocal;

    /// <summary>The state machine of the async function whose body is being emitted.</summary>
    private sealed class AsyncBody(TypeBuilder machine, FieldBuilder[] parameters)
    {
        public TypeBuilder Machine { get; } = machine;
        public FieldBuilder[] Params { get; } = parameters;
        public List<Label> Resumes { get; } = [];
        public Dictionary<LocalBuilder, FieldBuilder> Saved { get; } = [];
    }

    private AsyncBody? _async;
    /// <summary>Every IL local of the method being emitted, in declaration order; an 'await' saves and restores them.</summary>
    private readonly List<LocalBuilder> _allLocals = [];

    private ILGenerator _il = null!;
    private FnDecl _fn = null!;
    private Dictionary<string, Type> _gps = [];
    private readonly Dictionary<string, LocalBuilder> _locals = [];
    private readonly Dictionary<string, (int Arg, int Axis)> _dimSource = [];
    private readonly Stack<(Label Continue, Label Break, int TryDepth)> _loops = new();
    private int? _selfArg;

    /// <summary>
    /// Writes the assembly, its runtimeconfig and the runtime libraries. The file is
    /// <paramref name="outputFile"/> when set, otherwise <c>Module.dll</c> in <paramref name="outDir"/>.
    /// </summary>
    public string Emit(string outDir, bool verified, string? outputFile = null)
    {
        var dll = Path.GetFullPath(outputFile ?? Path.Combine(outDir, module.Name + ".dll"));
        outDir = Path.GetDirectoryName(dll)!;
        var assemblyName = Path.GetFileNameWithoutExtension(dll);
        var assembly = new PersistedAssemblyBuilder(new AssemblyName(assemblyName) { Version = new Version(1, 0, 0, 0) }, typeof(object).Assembly);
        _mb = assembly.DefineDynamicModule(module.Name);
        DefineTypes();

        var type = _mb.DefineType(module.Name, TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.Class);
        if (verified)
            type.SetCustomAttribute(new CustomAttributeBuilder(typeof(VerifiedAttribute).GetConstructor([typeof(string)])!, ["vsharpc"]));

        var publics = new Dictionary<FnDecl, MethodBuilder>();
        var contractCtor = typeof(ContractAttribute).GetConstructor([typeof(string), typeof(string)])!;
        foreach (var f in module.Fns.Where(f => f.Kind is FnKind.Fn or FnKind.Grad && !f.IsAbstract))
        {
            var checks = entryChecks && NeedsEntryCheck(f);
            var host = f.IsMethod ? _types[f.Owner!] : type;
            var name = f.Member ?? f.Name;
            var impl = DefineMethod(host, checks ? name + "$impl" : name, f, checks ? MethodAttributes.Assembly : MethodAttributes.Public, attributes: !checks);
            _impls[f] = impl;
            var pub = checks ? DefineMethod(host, name, f, MethodAttributes.Public, attributes: true) : impl;
            publics[f] = pub;
            foreach (var r in Requires(f))
                pub.SetCustomAttribute(new CustomAttributeBuilder(contractCtor, [entryChecks && Compilable(r) ? "requires" : "requires-unchecked", Text(r)]));
            foreach (var e in f.Ensures.Concat(f.Implements?.Ensures ?? [])) pub.SetCustomAttribute(new CustomAttributeBuilder(contractCtor, ["ensures", Text(e)]));
            foreach (var t in f.AllThrows)
                pub.SetCustomAttribute(new CustomAttributeBuilder(contractCtor, ["throws", t.When == null ? t.Name : $"{t.Name} when {Text(t.When)}"]));
        }
        foreach (var f in _impls.Keys)
        {
            EmitBody(f);
            if (publics[f] != _impls[f]) EmitEntryCheck(f, publics[f]);
        }
        foreach (var (t, info) in _checkedCtors) EmitCheckedCtor(t, info);
        var main = module.Fns.FirstOrDefault(f => f.Name == "main" && f.Kind == FnKind.Fn);
        var entry = main == null ? null : publics[main];
        if (main is { IsAsync: true })
        {
            entry = type.DefineMethod("main$entry", MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.HideBySig, typeof(void), Type.EmptyTypes);
            var il = entry.GetILGenerator();
            il.Emit(OpCodes.Call, publics[main]);
            il.Emit(OpCodes.Call, typeof(Async).GetMethod(nameof(Async.RunMain))!);
            il.Emit(OpCodes.Ret);
        }

        foreach (var t in _types.OrderBy(kv => kv.Key.Kind == TypeKind.Interface ? 0 : 1)) t.Value.CreateType();
        foreach (var c in _cases.Values) c.Type.CreateType();
        foreach (var e in _exceptions.Values) e.Type.CreateType();
        foreach (var m in _machines) m.CreateType();
        type.CreateType();

        var metadata = assembly.GenerateMetadata(out var ilStream, out var fieldData);
        metadata.GetOrAddString(Retarget.SystemRuntime);
        metadata.GetOrAddBlob(Retarget.SystemRuntimeToken);
        var pe = new ManagedPEBuilder(
            new PEHeaderBuilder(imageCharacteristics: entry == null ? Characteristics.Dll | Characteristics.ExecutableImage : Characteristics.ExecutableImage),
            new MetadataRootBuilder(metadata), ilStream, fieldData,
            entryPoint: entry == null ? default : MetadataTokens.MethodDefinitionHandle(entry.MetadataToken));
        var blob = new BlobBuilder();
        pe.Serialize(blob);
        var image = blob.ToArray();
        Retarget.ToSystemRuntime(image);

        Directory.CreateDirectory(outDir);
        File.WriteAllBytes(dll, image);
        var v = Environment.Version;
        File.WriteAllText(Path.Combine(outDir, assemblyName + ".runtimeconfig.json"),
            $$"""
            {
              "runtimeOptions": {
                "tfm": "net{{v.Major}}.{{v.Minor}}",
                "framework": { "name": "Microsoft.NETCore.App", "version": "{{v.Major}}.{{v.Minor}}.0" }
              }
            }
            """);
        CopyRuntime(typeof(Tensor<>).Assembly, outDir, []);
        return dll;
    }

    private static void CopyRuntime(Assembly asm, string outDir, HashSet<string> done)
    {
        if (!done.Add(asm.GetName().Name!) || string.IsNullOrEmpty(asm.Location)) return;
        File.Copy(asm.Location, Path.Combine(outDir, Path.GetFileName(asm.Location)), overwrite: true);
        var dir = Path.GetDirectoryName(asm.Location)!;
        foreach (var r in asm.GetReferencedAssemblies())
        {
            // A self-contained publish lays the shared framework next to the compiler. Loading
            // System.Private.CoreLib from that folder aborts the process, and the emitted program
            // gets the framework from its own runtimeconfig, not from these copies.
            if (r.Name is null || IsSharedFramework(r.Name)) continue;
            var file = Path.Combine(dir, r.Name + ".dll");
            if (File.Exists(file) && !done.Contains(r.Name!)) CopyRuntime(Assembly.LoadFrom(file), outDir, done);
        }
    }

    private static bool IsSharedFramework(string name) =>
        name is "netstandard" or "mscorlib"
        || name.StartsWith("System.", StringComparison.Ordinal)
        || name.StartsWith("Microsoft.", StringComparison.Ordinal);

    // ---------- types ----------

    private static string ClrName(string name, int arity) => arity == 0 ? name : $"{name}`{arity}";

    private void DefineTypes()
    {
        foreach (var t in module.Types.Where(t => t.Kind != TypeKind.Refinement))
        {
            var attrs = t.Kind == TypeKind.Interface ? TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract
                : TypeAttributes.Public | TypeAttributes.Class | (t.Kind == TypeKind.Union ? TypeAttributes.Abstract : TypeAttributes.Sealed);
            var tb = _mb.DefineType(ClrName(t.Name, t.TypeParams.Count), attrs);
            if (t.TypeParams.Count > 0) tb.DefineGenericParameters([.. t.TypeParams]);
            _types[t] = tb;
            if (t.Kind == TypeKind.Union) _baseCtors[t] = tb.DefineDefaultConstructor(MethodAttributes.Family);
            ApplyAttributes(t.Attrs, tb.SetCustomAttribute);
        }
        foreach (var t in module.Types.Where(t => t.Kind == TypeKind.Interface))
            foreach (var f in t.Methods)
                _abstracts[f] = DefineMethod(_types[t], f.Member!, f, MethodAttributes.Public | MethodAttributes.Abstract | MethodAttributes.Virtual | MethodAttributes.NewSlot, attributes: true);
        foreach (var t in module.Types.Where(t => t.Kind is TypeKind.Record or TypeKind.Union))
        {
            var tb = _types[t];
            if (t.Kind == TypeKind.Record)
            {
                foreach (var i in t.Interfaces) tb.AddInterfaceImplementation(_types[i]);
                var gps = TypeParamsOf(tb, t);
                var deferred = entryChecks && t.Invariants.Any(CtorCheckable);
                _records[t] = DefineFields(tb, t.Fields, gps, typeof(object).GetConstructor(Type.EmptyTypes)!, emitCtor: !deferred);
                if (deferred) _checkedCtors.Add((t, _records[t]));
                continue;
            }
            foreach (var c in t.Cases)
            {
                var cb = _mb.DefineType(ClrName(c.Name, t.TypeParams.Count), TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.Class);
                var gps = new Dictionary<string, Type>();
                Type parent = tb;
                if (t.TypeParams.Count > 0)
                {
                    var g = cb.DefineGenericParameters([.. t.TypeParams]);
                    for (var i = 0; i < g.Length; i++) gps[t.TypeParams[i]] = g[i];
                    parent = tb.MakeGenericType(g);
                }
                cb.SetParent(parent);
                var baseCtor = t.TypeParams.Count > 0 ? TypeBuilder.GetConstructor(parent, _baseCtors[t]) : _baseCtors[t];
                _cases[c] = DefineFields(cb, c.Fields, gps, baseCtor);
            }
        }
        foreach (var e in module.Exceptions.Where(e => !e.IsExtern))
        {
            var tb = _mb.DefineType(e.Name, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.Class, typeof(Exception));
            ApplyAttributes(e.Attrs, tb.SetCustomAttribute);
            _exceptions[e] = DefineFields(tb, e.Fields, [], typeof(Exception).GetConstructor(Type.EmptyTypes)!, structural: false);
        }
    }

    private static Dictionary<string, Type> TypeParamsOf(TypeBuilder tb, TypeDecl t)
    {
        var gps = new Dictionary<string, Type>();
        if (t.TypeParams.Count == 0) return gps;
        var args = tb.GetGenericArguments();
        for (var i = 0; i < args.Length; i++) gps[t.TypeParams[i]] = args[i];
        return gps;
    }

    /// <summary>
    /// Fields are internal (V# code reads them directly); .NET code sees one read-only property per field, which is
    /// what serializers such as System.Text.Json bind to. Equality and hashing are structural, as in the logic.
    /// </summary>
    private CaseInfo DefineFields(TypeBuilder tb, List<FieldDecl> fields, Dictionary<string, Type> gps, ConstructorInfo baseCtor, bool emitCtor = true, bool structural = true)
    {
        var types = fields.Select(f => Clr(f.Type, gps)).ToArray();
        var fbs = fields.Select((f, i) => tb.DefineField(f.Name + "$", types[i], FieldAttributes.Assembly | FieldAttributes.InitOnly)).ToArray();
        for (var i = 0; i < fields.Count; i++)
        {
            var prop = tb.DefineProperty(fields[i].Name, PropertyAttributes.None, types[i], null);
            ApplyAttributes(fields[i].Attrs, prop.SetCustomAttribute);
            var get = tb.DefineMethod("get_" + fields[i].Name, MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.HideBySig, types[i], Type.EmptyTypes);
            var gil = get.GetILGenerator();
            gil.Emit(OpCodes.Ldarg_0);
            gil.Emit(OpCodes.Ldfld, fbs[i]);
            gil.Emit(OpCodes.Ret);
            prop.SetGetMethod(get);
        }
        void Override(string name, Type ret, Type[] ps, string helper)
        {
            var m = tb.DefineMethod(name, MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.HideBySig, ret, ps);
            var mil = m.GetILGenerator();
            mil.Emit(OpCodes.Ldarg_0);
            if (ps.Length == 1) mil.Emit(OpCodes.Ldarg_1);
            mil.Emit(OpCodes.Call, typeof(Rt).GetMethod(helper, [typeof(object), .. ps])!);
            mil.Emit(OpCodes.Ret);
        }
        if (structural)
        {
            Override(nameof(Equals), typeof(bool), [typeof(object)], nameof(Rt.StructEquals));
            Override(nameof(GetHashCode), typeof(int), Type.EmptyTypes, nameof(Rt.StructHash));
            Override(nameof(ToString), typeof(string), Type.EmptyTypes, nameof(Rt.Format));
        }
        else Override("get_" + nameof(Exception.Message), typeof(string), Type.EmptyTypes, nameof(Rt.Format));
        var ctor = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, types);
        for (var i = 0; i < fields.Count; i++) ctor.DefineParameter(i + 1, ParameterAttributes.None, fields[i].Name);
        if (emitCtor)
        {
            var il = ctor.GetILGenerator();
            StoreFields(il, baseCtor, fbs);
            il.Emit(OpCodes.Ret);
        }
        return new CaseInfo(tb, ctor, fbs);
    }

    private static void StoreFields(ILGenerator il, ConstructorInfo baseCtor, FieldBuilder[] fbs)
    {
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Call, baseCtor);
        for (var i = 0; i < fbs.Length; i++)
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldarg, (short)(i + 1));
            il.Emit(OpCodes.Stfld, fbs[i]);
        }
    }

    /// <summary>
    /// A class constructor checks the invariant, because .NET code can construct the class without proving it. V#
    /// code has proved it already, so the check never fails for V# callers.
    /// </summary>
    private void EmitCheckedCtor(TypeDecl t, CaseInfo info)
    {
        _fn = new FnDecl { Name = t.Name, NameSpan = t.NameSpan };
        _il = ((ConstructorBuilder)info.Ctor).GetILGenerator();
        _locals.Clear();
        _gps = [];
        _dimSource.Clear();
        StoreFields(_il, typeof(object).GetConstructor(Type.EmptyTypes)!, info.Fields);
        _selfArg = 0;
        foreach (var inv in t.Invariants.Where(CtorCheckable))
        {
            var ok = _il.DefineLabel();
            E(inv);
            _il.Emit(OpCodes.Brtrue, ok);
            _il.Emit(OpCodes.Ldstr, t.Name);
            _il.Emit(OpCodes.Ldstr, "invariant " + Text(inv));
            _il.Emit(OpCodes.Call, typeof(Rt).GetMethod(nameof(Rt.Violation))!);
            _il.Emit(OpCodes.Throw);
            _il.MarkLabel(ok);
        }
        _selfArg = null;
        _il.Emit(OpCodes.Ret);
    }

    /// <summary>
    /// Whether a class invariant can be checked in the constructor. It may not run other V# functions, which could
    /// construct the class again and recurse.
    /// </summary>
    private static bool CtorCheckable(Expr e) => Compilable(e) && RunsNoCode(e);

    private static bool RunsNoCode(Expr e) => e switch
    {
        Call c => c.Target == null && c.Record == null && c.Args.All(RunsNoCode),
        WithExpr => false,
        Quant q => RunsNoCode(q.Lo!) && RunsNoCode(q.Hi!) && RunsNoCode(q.Body),
        Unary u => RunsNoCode(u.Operand),
        Binary b => RunsNoCode(b.Left) && RunsNoCode(b.Right),
        IfExpr i => RunsNoCode(i.Cond) && RunsNoCode(i.Then) && RunsNoCode(i.Else),
        Index i => RunsNoCode(i.Array) && RunsNoCode(i.At),
        FieldAccess f => RunsNoCode(f.Target),
        ArrayLit a => a.Elems.All(RunsNoCode),
        MatchExpr m => RunsNoCode(m.Scrutinee) && m.Arms.All(a => RunsNoCode(a.Body)),
        Lambda l => RunsNoCode(l.Body),
        Interp ip => ip.Parts.All(RunsNoCode),
        _ => true,
    };

    private static void ApplyAttributes(List<Attr> attrs, Action<CustomAttributeBuilder> set)
    {
        foreach (var a in attrs.Where(a => a.Ctor != null))
        {
            var props = a.Named.Where(n => n.Member is PropertyInfo).ToList();
            var fields = a.Named.Where(n => n.Member is FieldInfo).ToList();
            set(new CustomAttributeBuilder(a.Ctor!, a.CtorArgs,
                props.Select(p => (PropertyInfo)p.Member).ToArray(), props.Select(p => p.Value).ToArray(),
                fields.Select(f => (FieldInfo)f.Member).ToArray(), fields.Select(f => f.Value).ToArray()));
        }
    }

    private Type Clr(TType t, Dictionary<string, Type> gps) => t.Kind switch
    {
        TK.Int => typeof(long),
        TK.Int32 => typeof(int),
        TK.Bool => typeof(bool),
        TK.Float => typeof(double),
        TK.String => typeof(string),
        TK.Decimal => typeof(decimal),
        TK.Date => typeof(DateOnly),
        TK.Unit => typeof(void),
        TK.Array => Clr(t.Elem!, gps).MakeArrayType(),
        TK.Map => typeof(Map<,>).MakeGenericType(Clr(t.Key, gps), Clr(t.Value, gps)),
        TK.Set => typeof(Set<>).MakeGenericType(Clr(t.Elem!, gps)),
        TK.Tensor => t.ElemType == ElemType.Float64 ? typeof(Tensor<double>) : typeof(Tensor<float>),
        TK.Param => gps[t.Name!],
        TK.Named => t.Args.Count == 0 ? _types[t.Decl!] : _types[t.Decl!].MakeGenericType(t.Args.Select(a => Clr(a, gps)).ToArray()),
        _ => throw new InvalidOperationException($"no CLR type for {t}"),
    };

    private Type Clr(TType t) => Clr(t, _gps);

    private Type CaseType(CaseInfo info, TType owner) =>
        owner.Args.Count == 0 ? info.Type : info.Type.MakeGenericType(owner.Args.Select(Clr).ToArray());

    private static ConstructorInfo CtorOf(CaseInfo info, Type t) => t == info.Type ? info.Ctor : TypeBuilder.GetConstructor(t, info.Ctor);
    private static FieldInfo FieldOf(CaseInfo info, Type t, int index) => t == info.Type ? info.Fields[index] : TypeBuilder.GetField(t, info.Fields[index]);

    // ---------- methods ----------

    /// <summary>
    /// A module function is a static method. A class or interface method is an instance method whose receiver is its
    /// 'self' parameter, so V# parameter i is IL argument i either way.
    /// </summary>
    private MethodBuilder DefineMethod(TypeBuilder type, string name, FnDecl f, MethodAttributes visibility, bool attributes)
    {
        var flags = visibility | MethodAttributes.HideBySig;
        if (!f.IsMethod) flags |= MethodAttributes.Static;
        else if (f.Implements != null && visibility == MethodAttributes.Public) flags |= MethodAttributes.Virtual | MethodAttributes.Final | MethodAttributes.NewSlot;
        var m = type.DefineMethod(name, flags);
        var gps = new Dictionary<string, Type>();
        if (f.TypeParams.Count > 0)
        {
            var g = m.DefineGenericParameters([.. f.TypeParams]);
            for (var i = 0; i < g.Length; i++) gps[f.TypeParams[i]] = g[i];
        }
        var skip = f.IsMethod ? 1 : 0;
        m.SetSignature(RetClr(f, gps), null, null, f.Params.Skip(skip).Select(p => Clr(p.Type, gps)).ToArray(), null, null);
        for (var i = skip; i < f.Params.Count; i++)
        {
            var p = m.DefineParameter(i + 1 - skip, ParameterAttributes.None, f.Params[i].Name);
            if (attributes) ApplyAttributes(f.Params[i].Attrs, p.SetCustomAttribute);
        }
        if (attributes) ApplyAttributes(f.Attrs, m.SetCustomAttribute);
        return m;
    }

    /// <summary>The CLR return type: an async function returns a Task of its V# return type.</summary>
    private Type RetClr(FnDecl f, Dictionary<string, Type> gps)
    {
        var r = Clr(f.Ret, gps);
        if (!f.IsAsync) return r;
        return f.Ret.Kind == TK.Unit ? typeof(Task) : typeof(Task<>).MakeGenericType(r);
    }

    /// <summary>A function's preconditions, including those an implementation inherits from its interface method.</summary>
    private static IEnumerable<Expr> Requires(FnDecl f) => f.Requires.Concat(f.Implements?.Requires ?? []);

    private void Begin(FnDecl f, MethodBuilder m)
    {
        _fn = f;
        _il = m.GetILGenerator();
        _locals.Clear();
        _allLocals.Clear();
        _tryStack.Clear();
        _tryDepth = 0;
        _exit = null;
        _retLocal = null;
        _gps = [];
        if (m.IsGenericMethodDefinition)
        {
            var args = m.GetGenericArguments();
            for (var i = 0; i < args.Length; i++) _gps[f.TypeParams[i]] = args[i];
        }
        _dimSource.Clear();
        for (var p = 0; p < f.Params.Count; p++)
        {
            var t = f.Params[p].Type;
            if (t.Kind != TK.Tensor) continue;
            for (var k = 0; k < t.Dims.Count; k++)
                if (t.Dims[k].IsBareName) _dimSource.TryAdd(t.Dims[k].Name!, (p, k));
        }
    }

    private MethodInfo Callee(MethodBuilder m, IEnumerable<Type> typeArgs)
    {
        var args = typeArgs.ToArray();
        return args.Length == 0 ? m : m.MakeGenericMethod(args);
    }

    private void EmitBody(FnDecl f)
    {
        if (f.IsAsync) { EmitAsync(f); return; }
        Begin(f, _impls[f]);
        Block(f.Body);
        if (f.Ret.Kind == TK.Unit) _il.Emit(OpCodes.Ret);
        else Unreachable();
        EmitExit();
    }

    /// <summary>
    /// An async function becomes a state machine class whose Run method holds the body. The method itself
    /// copies its arguments into the machine and starts it. Each 'await' that finds its task unfinished
    /// saves the IL locals into fields, records where to resume and returns; the task's continuation runs
    /// the machine again, which restores the locals and carries on.
    /// </summary>
    private void EmitAsync(FnDecl f)
    {
        var result = f.Ret.Kind == TK.Unit ? null : Clr(f.Ret);
        var tb = _mb.DefineType($"{f.Name.Replace('.', '$')}$async", TypeAttributes.NotPublic | TypeAttributes.Sealed | TypeAttributes.Class, typeof(AsyncMachine));
        var fields = f.Params.Select(p => tb.DefineField($"{p.Name}$p", Clr(p.Type), FieldAttributes.Assembly)).ToArray();
        var ctor = tb.DefineDefaultConstructor(MethodAttributes.Public);
        var run = tb.DefineMethod(nameof(AsyncMachine.Run), MethodAttributes.Public | MethodAttributes.Virtual | MethodAttributes.HideBySig, typeof(void), Type.EmptyTypes);
        _machines.Add(tb);

        var il = _impls[f].GetILGenerator();
        var machine = il.DeclareLocal(tb);
        il.Emit(OpCodes.Newobj, ctor);
        il.Emit(OpCodes.Stloc, machine);
        for (var i = 0; i < fields.Length; i++)
        {
            il.Emit(OpCodes.Ldloc, machine);
            il.Emit(OpCodes.Ldarg, (short)i);
            il.Emit(OpCodes.Stfld, fields[i]);
        }
        il.Emit(OpCodes.Ldloc, machine);
        il.Emit(OpCodes.Call, result == null
            ? typeof(Async).GetMethod(nameof(Async.StartUnit))!
            : typeof(Async).GetMethod(nameof(Async.Start))!.MakeGenericMethod(result));
        il.Emit(OpCodes.Ret);

        Begin(f, run);
        _async = new AsyncBody(tb, fields);
        var dispatch = _il.DefineLabel();
        var start = _il.DefineLabel();
        _il.Emit(OpCodes.Br, dispatch);
        _il.MarkLabel(start);
        Block(f.Body);
        if (f.Ret.Kind == TK.Unit) CompleteAsync();
        else Unreachable();
        _il.MarkLabel(dispatch);
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Ldfld, typeof(AsyncMachine).GetField(nameof(AsyncMachine.State))!);
        _il.Emit(OpCodes.Switch, [start, .. _async.Resumes]);
        Unreachable();
        EmitExit();
        _async = null;
    }

    /// <summary>Completes the machine's task with the value on the stack (nothing for Unit) and returns.</summary>
    private void CompleteAsync()
    {
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Call, _fn.Ret.Kind == TK.Unit
            ? typeof(Async).GetMethod(nameof(Async.CompleteUnit))!
            : typeof(Async).GetMethod(nameof(Async.Complete))!.MakeGenericMethod(Clr(_fn.Ret)));
        ExitMethod();
    }

    /// <summary>Awaits the task on the stack (statement level, so nothing else is on it) and pushes its result.</summary>
    private void Await(TType ret)
    {
        var a = _async!;
        var unit = ret.Kind == TK.Unit;
        var task = Temp(unit ? typeof(Task) : typeof(Task<>).MakeGenericType(Clr(ret)));
        _il.Emit(OpCodes.Stloc, task);
        var ready = _il.DefineLabel();
        _il.Emit(OpCodes.Ldloc, task);
        _il.Emit(OpCodes.Callvirt, typeof(Task).GetProperty(nameof(Task.IsCompleted))!.GetMethod!);
        _il.Emit(OpCodes.Brtrue, ready);

        var live = _allLocals.ToList();
        foreach (var l in live)
        {
            if (!a.Saved.TryGetValue(l, out var field))
                a.Saved[l] = field = a.Machine.DefineField($"loc${l.LocalIndex}", l.LocalType, FieldAttributes.Private);
            _il.Emit(OpCodes.Ldarg_0);
            _il.Emit(OpCodes.Ldloc, l);
            _il.Emit(OpCodes.Stfld, field);
        }
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Ldc_I4, a.Resumes.Count + 1);
        _il.Emit(OpCodes.Stfld, typeof(AsyncMachine).GetField(nameof(AsyncMachine.State))!);
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Ldloc, task);
        _il.Emit(OpCodes.Call, typeof(AsyncMachine).GetMethod(nameof(AsyncMachine.Schedule))!);
        ExitMethod();

        // Inside try blocks, the dispatch cannot jump straight to the resume point: it enters each enclosing try at
        // its first instruction, whose own dispatch goes one level further in.
        var resume = _il.DefineLabel();
        var target = resume;
        for (var i = _tryStack.Count - 1; i >= 0; i--)
        {
            _tryStack[i].Inner.Add((a.Resumes.Count + 1, target));
            target = _tryStack[i].Entry;
        }
        a.Resumes.Add(target);
        _il.MarkLabel(resume);
        // Clear the state, so passing through an enclosing try's dispatch later is not mistaken for a resumption.
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Ldc_I4_M1);
        _il.Emit(OpCodes.Stfld, typeof(AsyncMachine).GetField(nameof(AsyncMachine.State))!);
        foreach (var l in live)
        {
            _il.Emit(OpCodes.Ldarg_0);
            _il.Emit(OpCodes.Ldfld, a.Saved[l]);
            _il.Emit(OpCodes.Stloc, l);
        }
        _il.MarkLabel(ready);
        _il.Emit(OpCodes.Ldloc, task);
        _il.Emit(OpCodes.Call, unit
            ? typeof(Async).GetMethod(nameof(Async.Wait))!
            : typeof(Async).GetMethod(nameof(Async.Result))!.MakeGenericMethod(Clr(ret)));
    }

    private void Unreachable()
    {
        _il.Emit(OpCodes.Ldstr, "unreachable");
        _il.Emit(OpCodes.Newobj, typeof(InvalidOperationException).GetConstructor([typeof(string)])!);
        _il.Emit(OpCodes.Throw);
    }

    private bool NeedsEntryCheck(FnDecl f) =>
        Requires(f).Any(Compilable) || f.Params.Any(p => p.Type.Refine?.Pred is { } pred && Compilable(pred));

    /// <summary>The public wrapper: check what an unverified .NET caller might violate, then call the implementation.</summary>
    private void EmitEntryCheck(FnDecl f, MethodBuilder pub)
    {
        Begin(f, pub);
        void Check(Expr cond, string text)
        {
            var ok = _il.DefineLabel();
            E(cond);
            _il.Emit(OpCodes.Brtrue, ok);
            _il.Emit(OpCodes.Ldstr, f.Name);
            _il.Emit(OpCodes.Ldstr, text);
            _il.Emit(OpCodes.Call, typeof(Rt).GetMethod(nameof(Rt.Violation))!);
            _il.Emit(OpCodes.Throw);
            _il.MarkLabel(ok);
        }
        for (var i = 0; i < f.Params.Count; i++)
        {
            var t = f.Params[i].Type;
            if (t.Refine?.Pred is not { } pred || !Compilable(pred)) continue;
            var saved = _gps;
            _gps = new Dictionary<string, Type>(_gps);
            foreach (var (k, v) in Checker.Map(t.Refine.TypeParams, t.RefineArgs)) _gps[k] = Clr(v, saved);
            _selfArg = i;
            Check(pred, $"{f.Params[i].Name}: {t} ({Text(pred)})");
            _selfArg = null;
            _gps = saved;
        }
        foreach (var r in Requires(f).Where(Compilable)) Check(r, Text(r));
        for (var i = 0; i < f.Params.Count; i++) _il.Emit(OpCodes.Ldarg, (short)i);
        _il.Emit(OpCodes.Call, Callee(_impls[f], f.TypeParams.Select(p => _gps[p])));
        _il.Emit(OpCodes.Ret);
    }

    /// <summary>Whether a specification expression can be evaluated at run time.</summary>
    private static bool Compilable(Expr e) => e switch
    {
        Quant q => q.Kind == QuantKind.Range && Compilable(q.Lo!) && Compilable(q.Hi!) && Compilable(q.Body),
        Hole => false,
        Var v => v.Kind is not (VarKind.Result or VarKind.Elem),
        Call c => (c.Target == null || c.Target.IsExecutable && c.Target.IsPure) && c.Name != "row_sum" && c.Args.All(Compilable),
        Unary u => Compilable(u.Operand),
        Binary b => Compilable(b.Left) && Compilable(b.Right),
        IfExpr i => Compilable(i.Cond) && Compilable(i.Then) && Compilable(i.Else),
        Index i => Compilable(i.Array) && Compilable(i.At),
        FieldAccess f => Compilable(f.Target),
        ArrayLit a => a.Elems.All(Compilable),
        MatchExpr m => Compilable(m.Scrutinee) && m.Arms.All(a => Compilable(a.Body)),
        Lambda l => Compilable(l.Body),
        WithExpr w => Compilable(w.Target) && w.Updates.All(u => Compilable(u.Value)),
        Interp ip => ip.Parts.All(Compilable),
        _ => true,
    };

    // ---------- statements ----------

    private void Block(List<Stmt> stmts)
    {
        foreach (var s in stmts) Statement(s);
    }

    private LocalBuilder Local(string name, TType type) => _locals[name] = Temp(Clr(type));

    /// <summary>Declares a local that shadows <paramref name="name"/> until <see cref="Restore"/> (loop and lambda variables).</summary>
    private LocalBuilder Scoped(string name, TType type, List<(string Name, LocalBuilder? Old)> undo)
    {
        undo.Add((name, _locals.GetValueOrDefault(name)));
        return Local(name, type);
    }

    private void Restore(List<(string Name, LocalBuilder? Old)> undo)
    {
        for (var k = undo.Count - 1; k >= 0; k--)
        {
            if (undo[k].Old is { } old) _locals[undo[k].Name] = old;
            else _locals.Remove(undo[k].Name);
        }
    }

    private LocalBuilder Temp(Type t)
    {
        var l = _il.DeclareLocal(t);
        _allLocals.Add(l);
        return l;
    }

    private LocalBuilder Store(Expr e)
    {
        var l = Temp(Clr(e.Type));
        E(e);
        _il.Emit(OpCodes.Stloc, l);
        return l;
    }

    private void ForStatement(For fr)
    {
        var undo = new List<(string Name, LocalBuilder? Old)>();
        var (top, next, end) = (_il.DefineLabel(), _il.DefineLabel(), _il.DefineLabel());
        var hi = Temp(typeof(long));
        LocalBuilder? arr = null;
        LocalBuilder i;
        if (fr.Source != null)
        {
            arr = Store(fr.Source);
            i = Scoped(fr.IndexName, TType.Int, undo);
            _il.Emit(OpCodes.Ldc_I8, 0L);
            _il.Emit(OpCodes.Stloc, i);
            _il.Emit(OpCodes.Ldloc, arr);
            _il.Emit(OpCodes.Ldlen);
            _il.Emit(OpCodes.Conv_I8);
            _il.Emit(OpCodes.Stloc, hi);
        }
        else
        {
            // Both bounds are evaluated once, before the index variable comes into scope.
            var lo = Store(fr.Lo!);
            E(fr.Hi!);
            _il.Emit(OpCodes.Stloc, hi);
            i = Scoped(fr.IndexName, TType.Int, undo);
            _il.Emit(OpCodes.Ldloc, lo);
            _il.Emit(OpCodes.Stloc, i);
        }
        var x = fr.Elem != null ? Scoped(fr.Elem, fr.ElemType, undo) : null;
        _il.MarkLabel(top);
        _il.Emit(OpCodes.Ldloc, i);
        _il.Emit(OpCodes.Ldloc, hi);
        _il.Emit(OpCodes.Bge, end);
        if (x != null)
        {
            _il.Emit(OpCodes.Ldloc, arr!);
            _il.Emit(OpCodes.Ldloc, i);
            _il.Emit(OpCodes.Conv_Ovf_I);
            _il.Emit(OpCodes.Ldelem, Clr(fr.ElemType));
            _il.Emit(OpCodes.Stloc, x);
        }
        _loops.Push((next, end, _tryDepth));
        Block(fr.Body);
        _loops.Pop();
        _il.MarkLabel(next);
        _il.Emit(OpCodes.Ldloc, i);
        _il.Emit(OpCodes.Ldc_I8, 1L);
        _il.Emit(OpCodes.Add);
        _il.Emit(OpCodes.Stloc, i);
        _il.Emit(OpCodes.Br, top);
        _il.MarkLabel(end);
        Restore(undo);
    }

    private void Statement(Stmt s)
    {
        if (s.Ghost) return;
        switch (s)
        {
            case Let l:
                E(l.Init);
                _il.Emit(OpCodes.Stloc, Local(l.Name, l.VarType));
                break;
            case Set st:
                E(st.Value);
                _il.Emit(OpCodes.Stloc, _locals[st.Name]);
                break;
            case If i:
            {
                var (els, end) = (_il.DefineLabel(), _il.DefineLabel());
                E(i.Cond);
                _il.Emit(OpCodes.Brfalse, els);
                Block(i.Then);
                _il.Emit(OpCodes.Br, end);
                _il.MarkLabel(els);
                if (i.Else != null) Block(i.Else);
                _il.MarkLabel(end);
                break;
            }
            case While w:
            {
                var (top, end) = (_il.DefineLabel(), _il.DefineLabel());
                _il.MarkLabel(top);
                E(w.Cond);
                _il.Emit(OpCodes.Brfalse, end);
                _loops.Push((top, end, _tryDepth));
                Block(w.Body);
                _loops.Pop();
                _il.Emit(OpCodes.Br, top);
                _il.MarkLabel(end);
                break;
            }
            case For fr:
                ForStatement(fr);
                break;
            case Break:
                _il.Emit(_tryDepth > _loops.Peek().TryDepth ? OpCodes.Leave : OpCodes.Br, _loops.Peek().Break);
                break;
            case Continue:
                _il.Emit(_tryDepth > _loops.Peek().TryDepth ? OpCodes.Leave : OpCodes.Br, _loops.Peek().Continue);
                break;
            case MatchStmt m:
                Match(m.Scrutinee, m.Arms.Select(a => (a.Pattern, (Action)(() => Block(a.Body)))).ToList());
                break;
            case Return r:
                E(r.Value);
                if (_async != null) CompleteAsync();
                else if (_tryDepth == 0) _il.Emit(OpCodes.Ret);
                else
                {
                    if (_fn.Ret.Kind != TK.Unit) _il.Emit(OpCodes.Stloc, _retLocal ??= Temp(Clr(_fn.Ret)));
                    _il.Emit(OpCodes.Leave, _exit ??= _il.DefineLabel());
                }
                break;
            case Throw th:
                E(th.Value);
                _il.Emit(OpCodes.Throw);
                break;
            case Try t:
                TryStatement(t);
                break;
            case Assert:
                break;
            case Print p:
                E(p.Value);
                _il.Emit(OpCodes.Call, typeof(Rt).GetMethod(nameof(Rt.Print))!.MakeGenericMethod(Clr(p.Value.Type)));
                break;
            case Do d:
                E(d.Call);
                if (d.Call.Type.Kind != TK.Unit) _il.Emit(OpCodes.Pop);
                break;
        }
    }

    /// <summary>
    /// Each IL catch handler only stores the exception and leaves; the catch body runs after the protected region.
    /// So a 'return', 'break' or 'await' in a catch body is ordinary code, and an exception thrown there is not
    /// caught by the same statement's other catches.
    /// </summary>
    private void TryStatement(Try t)
    {
        var types = t.Catches.Select(c => c.Decl!.Clr ?? _exceptions[c.Decl].Type).ToList();
        var caught = types.Select(Temp).ToList();
        var bodies = t.Catches.Select(_ => _il.DefineLabel()).ToList();
        var end = _il.DefineLabel();
        _il.BeginExceptionBlock();
        _tryDepth++;
        TryCtx? ctx = null;
        if (_async != null)
        {
            ctx = new TryCtx(_il.DefineLabel(), _il.DefineLabel(), _il.DefineLabel());
            _il.MarkLabel(ctx.Entry);
            _il.Emit(OpCodes.Br, ctx.Dispatch);
            _il.MarkLabel(ctx.Body);
            _tryStack.Add(ctx);
        }
        Block(t.Body);
        _il.Emit(OpCodes.Leave, end);
        if (ctx != null)
        {
            _tryStack.RemoveAt(_tryStack.Count - 1);
            _il.MarkLabel(ctx.Dispatch);
            foreach (var (state, target) in ctx.Inner)
            {
                _il.Emit(OpCodes.Ldarg_0);
                _il.Emit(OpCodes.Ldfld, typeof(AsyncMachine).GetField(nameof(AsyncMachine.State))!);
                _il.Emit(OpCodes.Ldc_I4, state);
                _il.Emit(OpCodes.Beq, target);
            }
            _il.Emit(OpCodes.Br, ctx.Body);
        }
        for (var i = 0; i < t.Catches.Count; i++)
        {
            _il.BeginCatchBlock(types[i]);
            _il.Emit(OpCodes.Stloc, caught[i]);
            _il.Emit(OpCodes.Leave, bodies[i]);
        }
        _il.EndExceptionBlock();
        _tryDepth--;
        for (var i = 0; i < t.Catches.Count; i++)
        {
            var c = t.Catches[i];
            _il.MarkLabel(bodies[i]);
            for (var k = 0; k < c.Binders.Count; k++)
            {
                if (c.Binders[k] == "_") continue;
                _il.Emit(OpCodes.Ldloc, caught[i]);
                if (c.Decl!.IsExtern) _il.Emit(OpCodes.Callvirt, typeof(Exception).GetProperty(nameof(Exception.Message))!.GetMethod!);
                else _il.Emit(OpCodes.Ldfld, _exceptions[c.Decl].Fields[k]);
                _il.Emit(OpCodes.Stloc, Local(c.Binders[k], c.Decl.Fields[k].Type));
            }
            Block(c.Body);
            _il.Emit(OpCodes.Br, end);
        }
        _il.MarkLabel(end);
    }

    /// <summary>Returns from the method: 'ret', or 'leave' to the exit label when inside a try block.</summary>
    private void ExitMethod()
    {
        if (_tryDepth == 0) _il.Emit(OpCodes.Ret);
        else _il.Emit(OpCodes.Leave, _exit ??= _il.DefineLabel());
    }

    /// <summary>The exit label's code, after the body: return the saved result.</summary>
    private void EmitExit()
    {
        if (_exit is not { } exit) return;
        _il.MarkLabel(exit);
        if (_retLocal != null) _il.Emit(OpCodes.Ldloc, _retLocal);
        _il.Emit(OpCodes.Ret);
    }

    private void Match(Expr scrutinee, List<(Pattern Pattern, Action Body)> arms)
    {
        var st = scrutinee.Type;
        var tmp = Temp(Clr(st));
        E(scrutinee);
        _il.Emit(OpCodes.Stloc, tmp);
        var end = _il.DefineLabel();
        foreach (var (p, body) in arms)
        {
            var next = _il.DefineLabel();
            if (p.Literal != null || p.Alternatives != null)
            {
                var hit = _il.DefineLabel();
                foreach (var alt in p.Alternatives ?? [p])
                {
                    if (alt.IsWildcard) { _il.Emit(OpCodes.Br, hit); continue; }
                    _il.Emit(OpCodes.Ldloc, tmp);
                    if (alt.Literal != null)
                    {
                        ELiteral(alt.Literal, st);
                        Eq(st);
                    }
                    else
                        _il.Emit(OpCodes.Isinst, CaseType(_cases[alt.Resolved!], st));
                    _il.Emit(OpCodes.Brtrue, hit);
                }
                _il.Emit(OpCodes.Br, next);
                _il.MarkLabel(hit);
            }
            else if (p.Resolved != null)
            {
                var info = _cases[p.Resolved];
                var ct = CaseType(info, st);
                _il.Emit(OpCodes.Ldloc, tmp);
                _il.Emit(OpCodes.Isinst, ct);
                _il.Emit(OpCodes.Brfalse, next);
                var map = Checker.Map(p.Resolved.Owner.TypeParams, st.Args);
                for (var k = 0; k < p.Binders.Count; k++)
                {
                    if (p.Binders[k] == "_") continue;
                    _il.Emit(OpCodes.Ldloc, tmp);
                    _il.Emit(OpCodes.Castclass, ct);
                    _il.Emit(OpCodes.Ldfld, FieldOf(info, ct, k));
                    _il.Emit(OpCodes.Stloc, Local(p.Binders[k], p.Resolved.Fields[k].Type.Subst(map, new Dictionary<string, Dim>())));
                }
            }
            body();
            _il.Emit(OpCodes.Br, end);
            _il.MarkLabel(next);
        }
        Unreachable();
        _il.MarkLabel(end);
    }

    // ---------- expressions ----------

    private void E(Expr e)
    {
        switch (e)
        {
            case IntLit or DecLit: ELiteral(e, e.Type); break;
            case FloatLit f: _il.Emit(OpCodes.Ldc_R8, f.Value); break;
            case BoolLit b: _il.Emit(b.Value ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0); break;
            case StrLit s: _il.Emit(OpCodes.Ldstr, s.Value); break;
            case UnitLit: break;
            case Interp ip:
                _il.Emit(OpCodes.Ldc_I4, ip.Parts.Count);
                _il.Emit(OpCodes.Newarr, typeof(string));
                for (var k = 0; k < ip.Parts.Count; k++)
                {
                    _il.Emit(OpCodes.Dup);
                    _il.Emit(OpCodes.Ldc_I4, k);
                    E(ip.Parts[k]);
                    if (ip.Parts[k] is not StrLit && ip.Parts[k].Type.Kind != TK.String) _il.Emit(OpCodes.Call, RtMethod(nameof(Rt.Str), Clr(ip.Parts[k].Type)));
                    _il.Emit(OpCodes.Stelem_Ref);
                }
                _il.Emit(OpCodes.Call, typeof(string).GetMethod(nameof(string.Concat), [typeof(string[])])!);
                break;
            case Var { Kind: VarKind.Const } v:
                E(v.Const!.Value);
                break;
            case Var v: EVar(v); break;
            case Unary { Op: "!" } u:
                E(u.Operand);
                Not();
                break;
            case Unary u when u.Type.Kind == TK.Float:
                E(u.Operand);
                _il.Emit(OpCodes.Neg);
                break;
            case Unary u when u.Type.Kind == TK.Decimal:
                E(u.Operand);
                _il.Emit(OpCodes.Call, typeof(decimal).GetMethod("op_UnaryNegation", [typeof(decimal)])!);
                break;
            case Unary u when u.Type.Kind == TK.Int32:
                _il.Emit(OpCodes.Ldc_I4_0);
                E(u.Operand);
                _il.Emit(OpCodes.Sub_Ovf);
                break;
            case WithExpr w:
            {
                var tt = w.Target.Type;
                var info = _records[tt.Decl!];
                var ct = Clr(tt);
                var target = Store(w.Target);
                var replaced = new LocalBuilder?[info.Fields.Length];
                for (var k = 0; k < w.Updates.Count; k++) replaced[w.Resolved[k]!.Index] = Store(w.Updates[k].Value);
                for (var k = 0; k < replaced.Length; k++)
                {
                    if (replaced[k] is { } l) { _il.Emit(OpCodes.Ldloc, l); continue; }
                    _il.Emit(OpCodes.Ldloc, target);
                    _il.Emit(OpCodes.Ldfld, FieldOf(info, ct, k));
                }
                _il.Emit(OpCodes.Newobj, CtorOf(info, ct));
                break;
            }
            case Unary u:
                _il.Emit(OpCodes.Ldc_I8, 0L);
                E(u.Operand);
                _il.Emit(OpCodes.Sub_Ovf);
                break;
            case Binary b: EBinary(b); break;
            case IfExpr i:
            {
                var (els, end) = (_il.DefineLabel(), _il.DefineLabel());
                E(i.Cond);
                _il.Emit(OpCodes.Brfalse, els);
                E(i.Then);
                _il.Emit(OpCodes.Br, end);
                _il.MarkLabel(els);
                E(i.Else);
                _il.MarkLabel(end);
                break;
            }
            case Index ix:
                E(ix.Array);
                E(ix.At);
                _il.Emit(OpCodes.Conv_Ovf_I);
                _il.Emit(OpCodes.Ldelem, Clr(ix.Type));
                break;
            case FieldAccess fa:
            {
                var tt = fa.Target.Type;
                var info = _records[tt.Decl!];
                E(fa.Target);
                _il.Emit(OpCodes.Ldfld, FieldOf(info, Clr(tt), fa.Resolved!.Index));
                break;
            }
            case ArrayLit a:
            {
                var et = Clr(a.Type.Elem!);
                _il.Emit(OpCodes.Ldc_I4, a.Elems.Count);
                _il.Emit(OpCodes.Newarr, et);
                for (var k = 0; k < a.Elems.Count; k++)
                {
                    _il.Emit(OpCodes.Dup);
                    _il.Emit(OpCodes.Ldc_I4, k);
                    E(a.Elems[k]);
                    _il.Emit(OpCodes.Stelem, et);
                }
                break;
            }
            case TensorLit t:
            {
                var f64 = t.Elem == ElemType.Float64;
                _il.Emit(OpCodes.Ldc_I4, t.Values.Count);
                _il.Emit(OpCodes.Newarr, f64 ? typeof(double) : typeof(float));
                for (var k = 0; k < t.Values.Count; k++)
                {
                    _il.Emit(OpCodes.Dup);
                    _il.Emit(OpCodes.Ldc_I4, k);
                    if (f64) { _il.Emit(OpCodes.Ldc_R8, t.Values[k]); _il.Emit(OpCodes.Stelem_R8); }
                    else { _il.Emit(OpCodes.Ldc_R4, (float)t.Values[k]); _il.Emit(OpCodes.Stelem_R4); }
                }
                Shape(t.Shape.Select(Dim.Of).ToList());
                var tt = f64 ? typeof(Tensor<double>) : typeof(Tensor<float>);
                _il.Emit(OpCodes.Newobj, tt.GetConstructor([f64 ? typeof(double[]) : typeof(float[]), typeof(int[])])!);
                break;
            }
            case Quant q: EQuant(q); break;
            case MatchExpr m:
                Match(m.Scrutinee, m.Arms.Select(a => (a.Pattern, (Action)(() => E(a.Body)))).ToList());
                break;
            case Call c: ECall(c); break;
            case Lambda: throw new InvalidOperationException("a lambda can only appear as a collection builtin's argument");
            default: throw new InvalidOperationException($"{e.GetType().Name} is specification-only and has no IL form");
        }
    }

    private void EVar(Var v)
    {
        switch (v.Kind)
        {
            case VarKind.Dim:
                LoadDim(v.Name);
                return;
            case VarKind.Self:
                _il.Emit(OpCodes.Ldarg, (short)_selfArg!.Value);
                return;
            case VarKind.Ctor:
            {
                var info = _cases[v.Ctor!];
                _il.Emit(OpCodes.Newobj, CtorOf(info, CaseType(info, v.Type)));
                return;
            }
        }
        if (_locals.TryGetValue(v.Name, out var local)) { _il.Emit(OpCodes.Ldloc, local); return; }
        LoadParam(_fn.Params.FindIndex(p => p.Name == v.Name));
    }

    private void LoadParam(int i)
    {
        if (_async == null) { _il.Emit(OpCodes.Ldarg, (short)i); return; }
        _il.Emit(OpCodes.Ldarg_0);
        _il.Emit(OpCodes.Ldfld, _async.Params[i]);
    }

    private void LoadDim(string name)
    {
        var (arg, axis) = _dimSource[name];
        var tt = _fn.Params[arg].Type.ElemType == ElemType.Float64 ? typeof(Tensor<double>) : typeof(Tensor<float>);
        LoadParam(arg);
        _il.Emit(OpCodes.Callvirt, tt.GetProperty(nameof(Tensor<float>.Shape))!.GetMethod!);
        _il.Emit(OpCodes.Ldc_I4, axis);
        _il.Emit(OpCodes.Ldelem_I4);
        _il.Emit(OpCodes.Conv_I8);
    }

    private void Dim1(Dim d)
    {
        if (d.Lit is { } v) _il.Emit(OpCodes.Ldc_I8, v);
        else if (d.Name != null) LoadDim(d.Name);
        else
        {
            Dim1(d.L!);
            Dim1(d.R!);
            _il.Emit(d.Op == '+' ? OpCodes.Add_Ovf : OpCodes.Mul_Ovf);
        }
    }

    private void Shape(IReadOnlyList<Dim> dims)
    {
        _il.Emit(OpCodes.Ldc_I4, dims.Count);
        _il.Emit(OpCodes.Newarr, typeof(int));
        for (var k = 0; k < dims.Count; k++)
        {
            _il.Emit(OpCodes.Dup);
            _il.Emit(OpCodes.Ldc_I4, k);
            Dim1(dims[k]);
            _il.Emit(OpCodes.Conv_Ovf_I4);
            _il.Emit(OpCodes.Stelem_I4);
        }
    }

    private static MethodInfo RtMethod(string name, params Type[] ps) =>
        typeof(Rt).GetMethod(name, ps) ?? throw new InvalidOperationException($"Rt.{name} not found");

    /// <summary>Loads an Int or Decimal literal as a value of type <paramref name="t"/> (literals adapt to Int32 and Decimal).</summary>
    private void ELiteral(Expr lit, TType t)
    {
        switch (lit)
        {
            case IntLit i when t.Kind == TK.Int32:
                _il.Emit(OpCodes.Ldc_I4, checked((int)i.Value));
                return;
            case IntLit i when t.Kind == TK.Decimal:
                _il.Emit(OpCodes.Ldc_I8, i.Value);
                _il.Emit(OpCodes.Call, typeof(decimal).GetMethod("op_Implicit", [typeof(long)])!);
                return;
            case IntLit i:
                _il.Emit(OpCodes.Ldc_I8, i.Value);
                return;
            case Unary { Op: "-", Operand: IntLit or DecLit } u when t.Kind is TK.Int32 or TK.Decimal:
                E(u.Operand is IntLit n ? new IntLit(-n.Value) { Type = t } : new DecLit(-((DecLit)u.Operand).Value, "") { Type = t });
                return;
            case DecLit d:
            {
                var bits = decimal.GetBits(d.Value);
                _il.Emit(OpCodes.Ldc_I4, bits[0]);
                _il.Emit(OpCodes.Ldc_I4, bits[1]);
                _il.Emit(OpCodes.Ldc_I4, bits[2]);
                _il.Emit(bits[3] < 0 ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Ldc_I4, (bits[3] >> 16) & 0xFF);
                _il.Emit(OpCodes.Newobj, typeof(decimal).GetConstructor([typeof(int), typeof(int), typeof(int), typeof(bool), typeof(byte)])!);
                return;
            }
            default:
                E(lit);
                return;
        }
    }

    /// <summary>Compares the two values on the stack for equality, as the verifier defines it for type <paramref name="t"/>.</summary>
    private void Eq(TType t)
    {
        switch (t.Kind)
        {
            case TK.String:
                _il.Emit(OpCodes.Call, RtMethod(nameof(Rt.StrEq), typeof(string), typeof(string)));
                return;
            case TK.Decimal or TK.Date:
            {
                var ct = Clr(t);
                _il.Emit(OpCodes.Call, ct.GetMethod("op_Equality", [ct, ct])!);
                return;
            }
            case TK.Named or TK.Param:
            {
                var ct = Clr(t);
                if (t.Kind == TK.Param)
                {
                    var r = Temp(ct);
                    _il.Emit(OpCodes.Stloc, r);
                    _il.Emit(OpCodes.Box, ct);
                    _il.Emit(OpCodes.Ldloc, r);
                    _il.Emit(OpCodes.Box, ct);
                }
                _il.Emit(OpCodes.Call, typeof(object).GetMethod(nameof(Equals), [typeof(object), typeof(object)])!);
                return;
            }
            default:
                _il.Emit(OpCodes.Ceq);
                return;
        }
    }

    private void Not()
    {
        _il.Emit(OpCodes.Ldc_I4_0);
        _il.Emit(OpCodes.Ceq);
    }

    private void EBinary(Binary b)
    {
        if (b.Op is "&&" or "||" or "==>")
        {
            // Short-circuit: 'a && b' skips b when a is false; 'a || b' and 'a ==> b' skip b when the answer is already true.
            var (shortcut, end) = (_il.DefineLabel(), _il.DefineLabel());
            E(b.Left);
            _il.Emit(b.Op == "||" ? OpCodes.Brtrue : OpCodes.Brfalse, shortcut);
            E(b.Right);
            _il.Emit(OpCodes.Br, end);
            _il.MarkLabel(shortcut);
            _il.Emit(b.Op == "&&" ? OpCodes.Ldc_I4_0 : OpCodes.Ldc_I4_1);
            _il.MarkLabel(end);
            return;
        }
        var lt = b.Left.Type;
        var isFloat = lt.Kind == TK.Float;
        E(b.Left);
        E(b.Right);
        if (b.Op is "==" or "!=")
        {
            Eq(lt);
            if (b.Op == "!=") Not();
            return;
        }
        if (lt.Kind == TK.String)
        {
            _il.Emit(OpCodes.Call, typeof(string).GetMethod(nameof(string.Concat), [typeof(string), typeof(string)])!);
            return;
        }
        if (lt.Kind is TK.Decimal or TK.Date)
        {
            var name = b.Op switch
            {
                "+" => "op_Addition", "-" => "op_Subtraction", "*" => "op_Multiply", "/" => "op_Division", "%" => "op_Modulus",
                "<" => "op_LessThan", ">" => "op_GreaterThan", "<=" => "op_LessThanOrEqual", _ => "op_GreaterThanOrEqual",
            };
            var t = Clr(lt);
            _il.Emit(OpCodes.Call, t.GetMethod(name, [t, t])!);
            return;
        }
        switch (b.Op)
        {
            // Int overflow traps instead of wrapping, so the verifier's unbounded integers are a sound model.
            case "+": _il.Emit(isFloat ? OpCodes.Add : OpCodes.Add_Ovf); break;
            case "-": _il.Emit(isFloat ? OpCodes.Sub : OpCodes.Sub_Ovf); break;
            case "*": _il.Emit(isFloat ? OpCodes.Mul : OpCodes.Mul_Ovf); break;
            case "/": _il.Emit(OpCodes.Div); break;
            case "%": _il.Emit(OpCodes.Rem); break;
            case "==": _il.Emit(OpCodes.Ceq); break;
            case "!=": _il.Emit(OpCodes.Ceq); Not(); break;
            case "<": _il.Emit(OpCodes.Clt); break;
            case ">": _il.Emit(OpCodes.Cgt); break;
            // For floats, the unordered forms make comparisons with NaN false, as IEEE 754 and the verifier require.
            case "<=": _il.Emit(isFloat ? OpCodes.Cgt_Un : OpCodes.Cgt); Not(); break;
            case ">=": _il.Emit(isFloat ? OpCodes.Clt_Un : OpCodes.Clt); Not(); break;
        }
    }

    /// <summary>A bounded quantifier, evaluated as a loop. Only used by entry checks.</summary>
    private void EQuant(Quant q)
    {
        if (q.Kind != QuantKind.Range) throw new InvalidOperationException("only bounded quantifiers can run");
        var i = Local(q.Binders[0].Name, TType.Int);
        var hi = Temp(typeof(long));
        var (top, done, decided, end) = (_il.DefineLabel(), _il.DefineLabel(), _il.DefineLabel(), _il.DefineLabel());
        E(q.Lo!);
        _il.Emit(OpCodes.Stloc, i);
        E(q.Hi!);
        _il.Emit(OpCodes.Stloc, hi);
        _il.MarkLabel(top);
        _il.Emit(OpCodes.Ldloc, i);
        _il.Emit(OpCodes.Ldloc, hi);
        _il.Emit(OpCodes.Bge, done);
        E(q.Body);
        _il.Emit(q.ForAll ? OpCodes.Brfalse : OpCodes.Brtrue, decided);
        _il.Emit(OpCodes.Ldloc, i);
        _il.Emit(OpCodes.Ldc_I8, 1L);
        _il.Emit(OpCodes.Add);
        _il.Emit(OpCodes.Stloc, i);
        _il.Emit(OpCodes.Br, top);
        _il.MarkLabel(done);
        _il.Emit(q.ForAll ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0);
        _il.Emit(OpCodes.Br, end);
        _il.MarkLabel(decided);
        _il.Emit(q.ForAll ? OpCodes.Ldc_I4_0 : OpCodes.Ldc_I4_1);
        _il.MarkLabel(end);
        _locals.Remove(q.Binders[0].Name);
    }

    private void ECall(Call c)
    {
        if (c.Exception is { } exc)
        {
            foreach (var a in c.Args) E(a);
            _il.Emit(OpCodes.Newobj, exc.Clr?.GetConstructor([typeof(string)]) ?? _exceptions[exc].Ctor);
            return;
        }
        if (c.Case != null || c.Record != null)
        {
            var info = c.Case != null ? _cases[c.Case] : _records[c.Record!];
            foreach (var a in c.Args) E(a);
            _il.Emit(OpCodes.Newobj, CtorOf(info, c.Case != null ? CaseType(info, c.Type) : Clr(c.Type)));
            return;
        }
        if (c.Target is { Kind: FnKind.Extern } ext)
        {
            foreach (var a in c.Args) E(a);
            _il.Emit(OpCodes.Call, ext.ExternMethod!);
            if (c.Awaited) Await(c.Type);
            return;
        }
        if (c.Target != null)
        {
            foreach (var a in c.Args) E(a);
            if (c.Target.IsAbstract) _il.Emit(OpCodes.Callvirt, _abstracts[c.Target]);
            else _il.Emit(OpCodes.Call, Callee(_impls[c.Target], c.Target.TypeParams.Select(p => Clr(c.TypeArgs[p]))));
            if (c.Awaited) Await(c.Type);
            return;
        }
        if (Checker.LambdaBuiltins.Contains(c.Name)) { ELambdaBuiltin(c); return; }
        if (ELibrary(c)) return;
        switch (c.Name)
        {
            case "len":
                E(c.Args[0]);
                _il.Emit(OpCodes.Ldlen);
                _il.Emit(OpCodes.Conv_I8);
                return;
            case "update" or "fill":
                foreach (var a in c.Args) E(a);
                var m = typeof(Rt).GetMethod(c.Name == "update" ? nameof(Rt.Update) : nameof(Rt.Fill))!;
                _il.Emit(OpCodes.Call, m.MakeGenericMethod(Clr(c.Type.Elem!)));
                return;
            case "to_float":
                E(c.Args[0]);
                _il.Emit(OpCodes.Conv_R8);
                return;
            case "trunc":
                E(c.Args[0]);
                _il.Emit(OpCodes.Conv_Ovf_I8);
                return;
        }
        var ops = _fn.Effects.Contains("device") ? typeof(DeviceOps) : typeof(TensorOps);
        var elem = c.Name == "full" ? c.Type.ElemType : c.Args[0].Type.ElemType;
        var method = ops.GetMethod(OpNames[c.Name])!.MakeGenericMethod(elem == ElemType.Float64 ? typeof(double) : typeof(float));
        if (c.Name == "full")
        {
            Shape(c.Type.Dims);
            E(c.Args[0]);
        }
        else
        {
            foreach (var a in c.Args) E(a);
            if (c.Name == "reshape") Shape(c.Type.Dims);
        }
        _il.Emit(OpCodes.Call, method);
    }

    // ---------- library builtins ----------

    private static bool IsBuilt(Type t) =>
        t is TypeBuilder or GenericTypeParameterBuilder
        || (t.HasElementType && IsBuilt(t.GetElementType()!))
        || (t.IsGenericType && t.GetGenericArguments().Any(IsBuilt));

    /// <summary>A method of a constructed runtime generic (Map, Set) whose type arguments may be types being built.</summary>
    private static MethodInfo On(Type t, string name) =>
        IsBuilt(t) ? TypeBuilder.GetMethod(t, t.GetGenericTypeDefinition().GetMethod(name)!) : t.GetMethod(name)!;

    private static MethodInfo RtGeneric(string name, params Type[] typeArgs) => typeof(Rt).GetMethod(name)!.MakeGenericMethod(typeArgs);

    private CaseInfo OptionCase(string name) =>
        _cases[module.Types.First(t => t.Prelude && t.Name == "Option").Cases.First(k => k.Name == name)];

    private void NewSome(TType option)
    {
        var info = OptionCase("Some");
        _il.Emit(OpCodes.Newobj, CtorOf(info, CaseType(info, option)));
    }

    private void NewNone(TType option)
    {
        var info = OptionCase("None");
        _il.Emit(OpCodes.Newobj, CtorOf(info, CaseType(info, option)));
    }

    /// <summary>Pushes 'Some(value)' if the bool on the stack is true, else 'None'; <paramref name="value"/> pushes the payload.</summary>
    private void SomeIf(TType option, Action value)
    {
        var (none, end) = (_il.DefineLabel(), _il.DefineLabel());
        _il.Emit(OpCodes.Brfalse, none);
        value();
        NewSome(option);
        _il.Emit(OpCodes.Br, end);
        _il.MarkLabel(none);
        NewNone(option);
        _il.MarkLabel(end);
    }

    private bool ELibrary(Call c)
    {
        Type S = typeof(string), L = typeof(long), D = typeof(DateOnly), M = typeof(decimal);
        void Args() { foreach (var a in c.Args) E(a); }
        void CallRt(string name, params Type[] ps) { Args(); _il.Emit(OpCodes.Call, RtMethod(name, ps)); }
        void Instance(string name) { Args(); _il.Emit(OpCodes.Callvirt, On(Clr(c.Args[0].Type), name)); }
        void Parse(string name, Type value)
        {
            var v = Temp(value);
            Args();
            _il.Emit(OpCodes.Ldloca, v);
            _il.Emit(OpCodes.Call, typeof(Rt).GetMethod(name)!);
            SomeIf(c.Type, () => _il.Emit(OpCodes.Ldloc, v));
        }
        switch (c.Name)
        {
            case "str_len": CallRt(nameof(Rt.StrLen), S); return true;
            case "str_sub": CallRt(nameof(Rt.Substring), S, L, L); return true;
            case "str_index_of": CallRt(nameof(Rt.IndexOf), S, S); return true;
            case "str_contains": CallRt(nameof(Rt.Contains), S, S); return true;
            case "str_starts_with": CallRt(nameof(Rt.StartsWith), S, S); return true;
            case "str_ends_with": CallRt(nameof(Rt.EndsWith), S, S); return true;
            case "str_trim": CallRt(nameof(Rt.Trim), S); return true;
            case "str_upper": CallRt(nameof(Rt.Upper), S); return true;
            case "str_lower": CallRt(nameof(Rt.Lower), S); return true;
            case "str_split": CallRt(nameof(Rt.Split), S, S); return true;
            case "str_join": CallRt(nameof(Rt.Join), typeof(string[]), S); return true;
            case "str_eq_ignore_case": CallRt(nameof(Rt.EqIgnoreCase), S, S); return true;
            case "str_is_blank": CallRt(nameof(Rt.IsBlank), S); return true;
            case "to_str": CallRt(nameof(Rt.Str), Clr(c.Args[0].Type)); return true;
            case "parse_int": Parse(nameof(Rt.TryParseInt), L); return true;
            case "parse_decimal": Parse(nameof(Rt.TryParseDecimal), M); return true;
            case "parse_date": Parse(nameof(Rt.TryParseDate), D); return true;
            case "parse_time": Parse(nameof(Rt.TryParseTime), L); return true;
            case "to_decimal":
                Args();
                _il.Emit(OpCodes.Call, M.GetMethod("op_Implicit", [Clr(c.Args[0].Type)])!);
                return true;
            case "to_int":
                Args();
                if (c.Args[0].Type.Kind == TK.Int32) _il.Emit(OpCodes.Conv_I8);
                else _il.Emit(OpCodes.Call, M.GetMethod(nameof(decimal.ToInt64), [M])!);
                return true;
            case "to_int32":
                Args();
                _il.Emit(OpCodes.Conv_Ovf_I4);
                return true;
            case "dec_round": CallRt(nameof(Rt.Round), M, L); return true;
            case "has_bit": CallRt(nameof(Rt.HasBit), L, L); return true;
            case "date": CallRt(nameof(Rt.MakeDate), L, L, L); return true;
            case "is_valid_date": CallRt(nameof(Rt.IsValidDate), L, L, L); return true;
            case "add_days": CallRt(nameof(Rt.AddDays), D, L); return true;
            case "days_between": CallRt(nameof(Rt.DaysBetween), D, D); return true;
            case "day_of_week": CallRt(nameof(Rt.DayOfWeek), D); return true;
            case "year": CallRt(nameof(Rt.Year), D); return true;
            case "month": CallRt(nameof(Rt.Month), D); return true;
            case "day": CallRt(nameof(Rt.Day), D); return true;
            case "append" or "concat":
                Args();
                _il.Emit(OpCodes.Call, RtGeneric(c.Name == "append" ? nameof(Rt.Append) : nameof(Rt.Concat), Clr(c.Type.Elem!)));
                return true;
            case "map_empty" or "set_empty":
                _il.Emit(OpCodes.Call, On(Clr(c.Type), "Empty"));
                return true;
            case "set_of":
                Args();
                _il.Emit(OpCodes.Call, On(Clr(c.Type), "Of"));
                return true;
            case "map_put": Instance("Put"); return true;
            case "map_remove": Instance("Remove"); return true;
            case "map_has" or "set_has": Instance("Has"); return true;
            case "map_get_or": Instance("GetOr"); return true;
            case "map_size" or "set_size": Instance("Size"); return true;
            case "map_keys": Instance("KeyArray"); return true;
            case "map_values": Instance("ValueArray"); return true;
            case "set_add": Instance("Add"); return true;
            case "set_items": Instance("ItemArray"); return true;
            case "map_get":
            {
                var mt = Clr(c.Args[0].Type);
                var m = Store(c.Args[0]);
                var k = Store(c.Args[1]);
                _il.Emit(OpCodes.Ldloc, m);
                _il.Emit(OpCodes.Ldloc, k);
                _il.Emit(OpCodes.Callvirt, On(mt, "Has"));
                SomeIf(c.Type, () =>
                {
                    _il.Emit(OpCodes.Ldloc, m);
                    _il.Emit(OpCodes.Ldloc, k);
                    _il.Emit(OpCodes.Callvirt, On(mt, "GetValue"));
                });
                return true;
            }
            case "is_some" or "is_none":
                E(c.Args[0]);
                _il.Emit(OpCodes.Isinst, CaseType(OptionCase("Some"), c.Args[0].Type));
                _il.Emit(OpCodes.Ldnull);
                _il.Emit(OpCodes.Cgt_Un);
                if (c.Name == "is_none") Not();
                return true;
            case "unwrap_or":
            {
                var some = OptionCase("Some");
                var st = CaseType(some, c.Args[0].Type);
                var o = Store(c.Args[0]);
                var (none, end) = (_il.DefineLabel(), _il.DefineLabel());
                _il.Emit(OpCodes.Ldloc, o);
                _il.Emit(OpCodes.Isinst, st);
                _il.Emit(OpCodes.Brfalse, none);
                _il.Emit(OpCodes.Ldloc, o);
                _il.Emit(OpCodes.Castclass, st);
                _il.Emit(OpCodes.Ldfld, FieldOf(some, st, 0));
                _il.Emit(OpCodes.Br, end);
                _il.MarkLabel(none);
                E(c.Args[1]);
                _il.MarkLabel(end);
                return true;
            }
        }
        return false;
    }

    /// <summary>
    /// Collection builtins inline their lambda into a loop over the array. Those whose result needs ordering or grouping
    /// first compute the lambda for every element into an array, then hand both arrays to a runtime helper.
    /// </summary>
    private void ELambdaBuiltin(Call c)
    {
        var elemT = c.Args[0].Type.Elem!;
        var elem = Clr(elemT);
        var arr = Store(c.Args[0]);
        var undo = new List<(string Name, LocalBuilder? Old)>();

        void Loop(Action<LocalBuilder> body, bool backwards = false)
        {
            var i = Temp(typeof(int));
            var (top, end) = (_il.DefineLabel(), _il.DefineLabel());
            if (backwards)
            {
                _il.Emit(OpCodes.Ldloc, arr);
                _il.Emit(OpCodes.Ldlen);
                _il.Emit(OpCodes.Conv_I4);
                _il.Emit(OpCodes.Ldc_I4_1);
                _il.Emit(OpCodes.Sub);
            }
            else _il.Emit(OpCodes.Ldc_I4_0);
            _il.Emit(OpCodes.Stloc, i);
            _il.MarkLabel(top);
            _il.Emit(OpCodes.Ldloc, i);
            if (backwards)
            {
                _il.Emit(OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Blt, end);
            }
            else
            {
                _il.Emit(OpCodes.Ldloc, arr);
                _il.Emit(OpCodes.Ldlen);
                _il.Emit(OpCodes.Conv_I4);
                _il.Emit(OpCodes.Bge, end);
            }
            body(i);
            _il.Emit(OpCodes.Ldloc, i);
            _il.Emit(OpCodes.Ldc_I4_1);
            _il.Emit(backwards ? OpCodes.Sub : OpCodes.Add);
            _il.Emit(OpCodes.Stloc, i);
            _il.Emit(OpCodes.Br, top);
            _il.MarkLabel(end);
        }
        void LoadElem(LocalBuilder i)
        {
            _il.Emit(OpCodes.Ldloc, arr);
            _il.Emit(OpCodes.Ldloc, i);
            _il.Emit(OpCodes.Ldelem, elem);
        }
        // Binds the lambda's element parameter to arr[i] and leaves the body's value on the stack.
        void Apply(Lambda lam, LocalBuilder x, LocalBuilder i)
        {
            LoadElem(i);
            _il.Emit(OpCodes.Stloc, x);
            E(lam.Body);
        }
        LocalBuilder Results(Lambda lam)
        {
            var rt = Clr(lam.Body.Type);
            var results = Temp(rt.MakeArrayType());
            var x = Scoped(lam.Params[^1], elemT, undo);
            var v = Temp(rt);
            _il.Emit(OpCodes.Ldloc, arr);
            _il.Emit(OpCodes.Ldlen);
            _il.Emit(OpCodes.Conv_I4);
            _il.Emit(OpCodes.Newarr, rt);
            _il.Emit(OpCodes.Stloc, results);
            Loop(i =>
            {
                Apply(lam, x, i);
                _il.Emit(OpCodes.Stloc, v);
                _il.Emit(OpCodes.Ldloc, results);
                _il.Emit(OpCodes.Ldloc, i);
                _il.Emit(OpCodes.Ldloc, v);
                _il.Emit(OpCodes.Stelem, rt);
            });
            return results;
        }

        var lam = (Lambda)c.Args[^1];
        switch (c.Name)
        {
            case "map":
                _il.Emit(OpCodes.Ldloc, Results(lam));
                break;
            case "filter":
                _il.Emit(OpCodes.Ldloc, arr);
                _il.Emit(OpCodes.Ldloc, Results(lam));
                _il.Emit(OpCodes.Call, RtGeneric(nameof(Rt.Filter), elem));
                break;
            case "any" or "all":
            {
                var any = c.Name == "any";
                var result = Temp(typeof(bool));
                var x = Scoped(lam.Params[0], elemT, undo);
                var (decided, end) = (_il.DefineLabel(), _il.DefineLabel());
                Loop(i =>
                {
                    Apply(lam, x, i);
                    _il.Emit(any ? OpCodes.Brtrue : OpCodes.Brfalse, decided);
                });
                _il.Emit(any ? OpCodes.Ldc_I4_0 : OpCodes.Ldc_I4_1);
                _il.Emit(OpCodes.Br, end);
                _il.MarkLabel(decided);
                _il.Emit(any ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0);
                _il.MarkLabel(end);
                break;
            }
            case "count":
            {
                var n = Temp(typeof(long));
                var x = Scoped(lam.Params[0], elemT, undo);
                _il.Emit(OpCodes.Ldc_I8, 0L);
                _il.Emit(OpCodes.Stloc, n);
                Loop(i =>
                {
                    var skip = _il.DefineLabel();
                    Apply(lam, x, i);
                    _il.Emit(OpCodes.Brfalse, skip);
                    _il.Emit(OpCodes.Ldloc, n);
                    _il.Emit(OpCodes.Ldc_I8, 1L);
                    _il.Emit(OpCodes.Add);
                    _il.Emit(OpCodes.Stloc, n);
                    _il.MarkLabel(skip);
                });
                _il.Emit(OpCodes.Ldloc, n);
                break;
            }
            case "find" or "find_last":
            {
                var x = Scoped(lam.Params[0], elemT, undo);
                var (found, end) = (_il.DefineLabel(), _il.DefineLabel());
                Loop(i =>
                {
                    Apply(lam, x, i);
                    _il.Emit(OpCodes.Brtrue, found);
                }, backwards: c.Name == "find_last");
                NewNone(c.Type);
                _il.Emit(OpCodes.Br, end);
                _il.MarkLabel(found);
                _il.Emit(OpCodes.Ldloc, x);
                NewSome(c.Type);
                _il.MarkLabel(end);
                break;
            }
            case "sum_by":
            {
                var t = c.Type;
                var acc = Temp(Clr(t));
                var v = Temp(Clr(t));
                var x = Scoped(lam.Params[0], elemT, undo);
                if (t.Kind == TK.Float) _il.Emit(OpCodes.Ldc_R8, 0.0);
                else ELiteral(new IntLit(0), t);
                _il.Emit(OpCodes.Stloc, acc);
                Loop(i =>
                {
                    Apply(lam, x, i);
                    _il.Emit(OpCodes.Stloc, v);
                    _il.Emit(OpCodes.Ldloc, acc);
                    _il.Emit(OpCodes.Ldloc, v);
                    if (t.Kind == TK.Decimal) _il.Emit(OpCodes.Call, typeof(decimal).GetMethod("op_Addition", [typeof(decimal), typeof(decimal)])!);
                    else _il.Emit(t.Kind == TK.Float ? OpCodes.Add : OpCodes.Add_Ovf);
                    _il.Emit(OpCodes.Stloc, acc);
                });
                _il.Emit(OpCodes.Ldloc, acc);
                break;
            }
            case "min_by" or "max_by":
            {
                var keys = Results(lam);
                var best = Temp(typeof(int));
                _il.Emit(OpCodes.Ldloc, keys);
                _il.Emit(c.Name == "max_by" ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Call, RtGeneric(nameof(Rt.BestIndex), Clr(lam.Body.Type)));
                _il.Emit(OpCodes.Stloc, best);
                _il.Emit(OpCodes.Ldloc, best);
                _il.Emit(OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Clt);
                Not();
                SomeIf(c.Type, () => LoadElem(best));
                break;
            }
            case "sort_by" or "sort_by_desc":
            {
                var keys = Results(lam);
                _il.Emit(OpCodes.Ldloc, arr);
                _il.Emit(OpCodes.Ldloc, keys);
                _il.Emit(c.Name == "sort_by_desc" ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Call, RtGeneric(nameof(Rt.SortBy), elem, Clr(lam.Body.Type)));
                break;
            }
            case "group_by":
            {
                var keys = Results(lam);
                _il.Emit(OpCodes.Ldloc, arr);
                _il.Emit(OpCodes.Ldloc, keys);
                _il.Emit(OpCodes.Call, RtGeneric(nameof(Rt.GroupBy), elem, Clr(lam.Body.Type)));
                break;
            }
            case "to_map":
            {
                var keyLam = (Lambda)c.Args[1];
                var keys = Results(keyLam);
                var values = Results(lam);
                _il.Emit(OpCodes.Ldloc, keys);
                _il.Emit(OpCodes.Ldloc, values);
                _il.Emit(OpCodes.Call, RtGeneric(nameof(Rt.ToMap), Clr(keyLam.Body.Type), Clr(lam.Body.Type)));
                break;
            }
            case "fold":
            {
                var init = Store(c.Args[1]);
                var acc = Scoped(lam.Params[0], c.Type, undo);
                var x = Scoped(lam.Params[1], elemT, undo);
                _il.Emit(OpCodes.Ldloc, init);
                _il.Emit(OpCodes.Stloc, acc);
                Loop(i =>
                {
                    Apply(lam, x, i);
                    _il.Emit(OpCodes.Stloc, acc);
                });
                _il.Emit(OpCodes.Ldloc, acc);
                break;
            }
        }
        Restore(undo);
    }

    private string Text(Expr e)
    {
        if (e.Span.File < 0 || e.Span.File >= sources.Count) return "<generated>";
        var source = sources[e.Span.File];
        return e.Span.End <= source.Length && e.Span.Start < e.Span.End ? source[e.Span.Start..e.Span.End] : "<generated>";
    }
}
