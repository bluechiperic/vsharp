using System.Reflection;

namespace VSharp.Compiler;

/// <summary>Name resolution, types, tensor shapes, effects, ghost code and the structural rules that the verifier relies on.</summary>
public sealed class Checker(ModuleDecl module, DiagnosticBag diags, IReadOnlyList<string>? references = null)
{
    /// <summary>Members of System.Object, which a method cannot be named after.</summary>
    private static readonly HashSet<string> ObjectMembers = ["Equals", "GetHashCode", "ToString", "GetType", "Finalize", "MemberwiseClone"];

    /// <summary>The original builtins, whose names cannot be used for variables either.</summary>
    private static readonly HashSet<string> CoreBuiltins =
    [
        "len", "update", "fill", "to_float", "trunc",
        "matmul", "add", "sub", "mul", "scale", "add_bias", "relu", "tanh", "sigmoid", "softmax", "transpose", "reshape", "full",
        "sum", "to_f32", "to_f64", "relu_grad", "tanh_grad", "sigmoid_grad", "softmax_grad", "sum_rows", "row_sum",
    ];

    /// <summary>Builtins that take a lambda; the lambda is inlined, never a value.</summary>
    public static readonly HashSet<string> LambdaBuiltins =
    [
        "map", "filter", "any", "all", "count", "find", "find_last", "sum_by", "min_by", "max_by", "sort_by", "sort_by_desc",
        "group_by", "to_map", "fold",
    ];

    /// <summary>Strings, decimals, dates, collections, maps, sets and options. Variables may reuse these names.</summary>
    private static readonly HashSet<string> LibraryBuiltins =
    [
        "str_len", "str_sub", "str_index_of", "str_contains", "str_starts_with", "str_ends_with", "str_trim", "str_upper",
        "str_lower", "str_split", "str_join", "str_eq_ignore_case", "str_is_blank", "to_str", "parse_int", "parse_decimal",
        "parse_date", "parse_time", "to_decimal", "dec_round", "to_int", "to_int32", "has_bit",
        "date", "is_valid_date", "add_days", "days_between", "day_of_week", "year", "month", "day",
        "append", "concat",
        "map_empty", "map_put", "map_get", "map_has", "map_remove", "map_size", "map_keys", "map_values", "map_get_or",
        "set_empty", "set_of", "set_add", "set_has", "set_size", "set_items",
        "is_some", "is_none", "unwrap_or",
        .. LambdaBuiltins,
    ];

    public static readonly HashSet<string> Builtins = [.. CoreBuiltins, .. LibraryBuiltins];

    /// <summary>Tensor builtins whose execution is dispatched to the device inside a 'device' function.</summary>
    public static readonly HashSet<string> TensorBuiltins =
    [
        "matmul", "add", "sub", "mul", "scale", "add_bias", "relu", "tanh", "sigmoid", "softmax", "transpose", "reshape", "full",
        "sum", "to_f32", "to_f64", "relu_grad", "tanh_grad", "sigmoid_grad", "softmax_grad", "sum_rows",
    ];

    private static readonly HashSet<string> ReservedTypes =
        ["Int", "Bool", "Unit", "Float", "Array", "Tensor", "Float32", "Float64", "String", "Date", "Decimal", "Int32", "Map", "Set"];

    private sealed record VarInfo(TType Type, bool Mutable, bool Ghost, VarKind Kind);

    private readonly Dictionary<string, TypeDecl> _types = [];
    private readonly Dictionary<string, FnDecl> _fns = [];
    private readonly Dictionary<string, CaseDecl> _cases = [];
    private readonly Dictionary<string, ConstDecl> _consts = [];
    private readonly Dictionary<string, ExceptionDecl> _exceptions = [];
    /// <summary>The try statements whose block is being checked, outermost first.</summary>
    private readonly List<Try> _tries = [];
    /// <summary>Catch clauses that some throw site can reach.</summary>
    private readonly HashSet<Catch> _reached = [];
    private readonly HashSet<string> _global = [];
    private int _loops;
    /// <summary>While checking a constant: the constants declared before it, which are the only ones it may use.</summary>
    private HashSet<ConstDecl>? _earlierConsts;

    private FnDecl _cur = null!;
    private readonly List<Dictionary<string, VarInfo>> _scopes = [];
    private readonly HashSet<string> _used = [];
    private HashSet<FnDecl> _callSink = [];
    private bool _inSpec;
    private bool _ghost;
    private bool _allowResult;
    private TType? _selfType;
    private bool _inDo;

    public IReadOnlyDictionary<string, FnDecl> Functions => _fns;

    public void Check()
    {
        Register();
        foreach (var t in module.Types.Where(t => t.Kind == TypeKind.Refinement))
        {
            var r = Resolve(t.Base!, t.TypeParams.ToHashSet(), new HashSet<string>(), t.NameSpan, allowRefine: false);
            t.Base = r;
        }
        foreach (var t in module.Types)
        {
            foreach (var f in t.Fields) f.Type = ResolveField(f, t);
            foreach (var c in t.Cases)
                foreach (var f in c.Fields) f.Type = ResolveField(f, t);
        }
        ResolveExceptions();
        _fieldsResolved = true;
        foreach (var (t, span) in _pendingKeys) CheckKey(t, span);
        ResolveInterfaces();
        foreach (var c in module.Consts) c.Type = Resolve(c.Type, new HashSet<string>(), new HashSet<string>(), c.NameSpan);
        foreach (var f in module.Fns.Where(f => f.Kind != FnKind.Grad)) ResolveSignature(f);
        CheckImplementations();
        var grads = module.Fns.Where(f => f.Kind == FnKind.Grad).Where(g => Grad.Signature(g, _fns.GetValueOrDefault(g.GradOf!), diags)).ToList();
        foreach (var t in module.Types.Where(t => t.Kind == TypeKind.Refinement)) CheckRefinement(t);
        foreach (var t in module.Types.Where(t => t.Invariants.Count > 0)) CheckInvariants(t);
        CheckConsts();
        foreach (var f in module.Fns.Where(f => f.Kind != FnKind.Grad)) CheckFn(f);
        if (!diags.HasErrors)
            foreach (var g in grads)
                if (new Grad(diags).Body(g, _fns[g.GradOf!]))
                    CheckFn(g);
        LinkInterfaces();
        CheckRecursion();
        BindAttributes();
    }

    // ---------- classes, interfaces and attributes ----------

    private void ResolveInterfaces()
    {
        foreach (var t in module.Types.Where(t => t.IsClass))
            foreach (var (name, span) in t.ImplementsNames)
            {
                if (!_types.TryGetValue(name, out var i)) diags.Error("TN2001", span, $"unknown interface '{name}'");
                else if (i.Kind != TypeKind.Interface) diags.Error("TN2027", span, $"'{name}' is not an interface", "A class implements interfaces; it cannot extend a record, union or class.");
                else if (t.Interfaces.Contains(i)) diags.Error("TN2027", span, $"interface '{name}' is listed twice");
                else t.Interfaces.Add(i);
            }
    }

    private static string Signature(FnDecl f) =>
        $"fn {f.Member ?? f.Name}({string.Join(", ", f.Params.Select(p => p.Name == "self" && f.IsMethod ? "self" : $"{p.Name}: {p.Type}"))}) -> {f.Ret}" +
        (f.Effects.Count > 0 ? " effects " + string.Join(", ", f.Effects) : "");

    /// <summary>
    /// A class method implements the interface method of the same name. It repeats the signature exactly, inherits the
    /// interface's 'requires' (it may not add its own, so every caller of the interface can call it) and is proved
    /// against the interface's 'ensures' as well as its own.
    /// </summary>
    private void CheckImplementations()
    {
        foreach (var t in module.Types.Where(t => t.IsClass))
            foreach (var i in t.Interfaces)
                foreach (var im in i.Methods)
                {
                    var cm = t.Methods.FirstOrDefault(m => m.Member == im.Member);
                    if (cm == null)
                    {
                        diags.Error("TN2027", t.NameSpan, $"class '{t.Name}' does not implement '{im.Name}'", $"Add the method: {Signature(im)} {{ ... }}");
                        continue;
                    }
                    if (cm.Kind != FnKind.Fn)
                    {
                        diags.Error("TN2027", cm.NameSpan, $"'{cm.Name}' implements '{im.Name}', so it must be an ordinary 'fn'");
                        continue;
                    }
                    if (cm.Implements != null)
                    {
                        diags.Error("TN2027", cm.NameSpan, $"'{cm.Name}' cannot implement both '{cm.Implements.Name}' and '{im.Name}'", "Rename one of the interface methods.");
                        continue;
                    }
                    var same = cm.Params.Count == im.Params.Count && cm.Ret.ToString() == im.Ret.ToString()
                        && cm.Params.Skip(1).Zip(im.Params.Skip(1)).All(p => p.First.Name == p.Second.Name && p.First.Type.ToString() == p.Second.Type.ToString());
                    if (!same)
                        diags.Error("TN2027", cm.NameSpan, $"'{cm.Name}' must have the signature of '{im.Name}': {Signature(im)}",
                            "An implementation repeats the interface method's parameter names, parameter types and result type.");
                    if (cm.Requires.Count > 0)
                        diags.Error("TN2027", cm.Requires[0].Span, $"'{cm.Name}' inherits the 'requires' of '{im.Name}' and cannot add its own",
                            "Code that calls the interface only knows the interface's preconditions. Move the condition to the interface, or handle it in the body.");
                    foreach (var eff in cm.Effects.Where(e => !im.Effects.Contains(e)))
                        diags.Error("TN2027", cm.NameSpan, $"'{cm.Name}' has the {eff} effect, which '{im.Name}' does not declare");
                    if (im.IsAsync && !cm.IsAsync)
                        diags.Error("TN2027", cm.NameSpan, $"'{cm.Name}' must be async, like '{im.Name}'", "In .NET both return a Task. Add 'effects async'.");
                    foreach (var tc in cm.Throws.Where(tc => tc.Decl != null && !im.Throws.Any(o => o.Decl != null && o.Decl.Covers(tc.Decl))))
                        diags.Error("TN2027", tc.Span, $"'{cm.Name}' declares 'throws {tc.Name}', which '{im.Name}' does not",
                            "Code that calls the interface only expects the interface's exceptions. Declare it on the interface method, or catch it.");
                    cm.Implements = im;
                }
    }

    private void CheckInvariants(TypeDecl t)
    {
        _cur = new FnDecl { Name = t.Name, NameSpan = t.NameSpan };
        ResetScopes();
        _callSink = t.Calls;
        _selfType = TType.Named(t, []);
        _inSpec = true;
        foreach (var inv in t.Invariants) Expect(inv, TType.Bool);
        _inSpec = false;
        _selfType = null;
    }

    /// <summary>
    /// Adds the call-graph edges of dynamic dispatch: an interface method can run any implementation, and an
    /// implementation relies on the functions its inherited contract mentions.
    /// </summary>
    private void LinkInterfaces()
    {
        var impls = module.Types.Where(t => t.IsClass).SelectMany(t => t.Methods).Where(m => m.Implements != null).ToList();
        foreach (var cm in impls) cm.Calls.UnionWith(cm.Implements!.Calls);
        foreach (var cm in impls) cm.Implements!.Calls.Add(cm);
    }

    private void BindAttributes()
    {
        if (!module.Types.Any(t => t.Attrs.Count > 0 || t.Fields.Concat(t.Cases.SelectMany(c => c.Fields)).Any(f => f.Attrs.Count > 0))
            && !module.Fns.Any(f => f.Attrs.Count > 0 || f.Params.Any(p => p.Attrs.Count > 0))
            && !module.Exceptions.Any(e => e.Attrs.Count > 0 || e.Fields.Any(f => f.Attrs.Count > 0)))
            return;
        var binder = new AttributeBinder(diags, module.Uses.Select(u => u.Namespace).ToList(), references ?? []);
        foreach (var e in module.Exceptions)
        {
            if (e.IsExtern)
            {
                if (e.Attrs.Count > 0) diags.Error("TN2026", e.Attrs[0].Span, "an exception bound to a .NET type cannot have attributes", "The .NET type is already defined.");
                continue;
            }
            binder.Bind(e.Attrs, AttrTarget.Class, "an exception");
            foreach (var f in e.Fields) binder.Bind(f.Attrs, AttrTarget.Property, "a field");
        }
        foreach (var t in module.Types.Where(t => !t.Prelude))
        {
            if (t.Kind == TypeKind.Refinement)
            {
                if (t.Attrs.Count > 0) diags.Error("TN2026", t.Attrs[0].Span, "a refinement type cannot have attributes", "A refinement type is its base type in the assembly.");
                continue;
            }
            binder.Bind(t.Attrs, t.Kind == TypeKind.Interface ? AttrTarget.Interface : AttrTarget.Class,
                t.Kind == TypeKind.Interface ? "an interface" : t.IsClass ? "a class" : t.Kind == TypeKind.Union ? "a union" : "a record");
            foreach (var f in t.Fields.Concat(t.Cases.SelectMany(c => c.Fields))) binder.Bind(f.Attrs, AttrTarget.Property, "a field");
        }
        foreach (var f in module.Fns.Where(f => !f.Prelude))
        {
            if (f.Kind is not (FnKind.Fn or FnKind.Grad))
            {
                var first = f.Attrs.Concat(f.Params.SelectMany(p => p.Attrs)).FirstOrDefault();
                if (first != null)
                    diags.Error("TN2026", first.Span, $"'{f.Name}' is not compiled to a .NET method, so it cannot have attributes",
                        "Spec functions and lemmas are erased, and extern functions are .NET methods already.");
                continue;
            }
            binder.Bind(f.Attrs, AttrTarget.Method, f.IsMethod ? "a method" : "a function");
            foreach (var p in f.Params) binder.Bind(p.Attrs, AttrTarget.Parameter, "a parameter");
        }
    }

    // ---------- registration and resolution ----------

    private void Register()
    {
        void Claim(string name, Span span)
        {
            if (Builtins.Contains(name) || ReservedTypes.Contains(name) || !_global.Add(name))
                diags.Error("TN2004", span, $"the name '{name}' is already used in this module or is reserved");
        }
        foreach (var t in module.Types)
        {
            Claim(t.Name, t.NameSpan);
            _types[t.Name] = t;
            for (var i = 0; i < t.Cases.Count; i++)
            {
                var c = t.Cases[i];
                Claim(c.Name, c.Span);
                c.Owner = t;
                c.Index = i;
                _cases[c.Name] = c;
                for (var k = 0; k < c.Fields.Count; k++) c.Fields[k].Index = k;
            }
            for (var k = 0; k < t.Fields.Count; k++) t.Fields[k].Index = k;
            if (t.Kind == TypeKind.Union && t.Cases.Count == 0) diags.Error("TN2016", t.NameSpan, "a union needs at least one case");
            if (t.Fields.Select(f => f.Name).Distinct().Count() != t.Fields.Count || t.Cases.Any(c => c.Fields.Select(f => f.Name).Distinct().Count() != c.Fields.Count))
                diags.Error("TN2004", t.NameSpan, $"field names in '{t.Name}' must be distinct");
            foreach (var m in t.Methods)
                if (ObjectMembers.Contains(m.Member!) || t.Fields.Any(f => f.Name == m.Member))
                    diags.Error("TN2004", m.NameSpan, $"'{t.Name}' cannot have a method named '{m.Member}'",
                        ObjectMembers.Contains(m.Member!) ? "Every .NET object already has a member with that name." : "A field has that name.");
            module.Fns.AddRange(t.Methods.Where(m => !module.Fns.Contains(m)));
        }
        foreach (var f in module.Fns)
        {
            Claim(f.Name, f.NameSpan);
            _fns[f.Name] = f;
        }
        foreach (var c in module.Consts)
        {
            Claim(c.Name, c.NameSpan);
            _consts[c.Name] = c;
        }
        foreach (var e in module.Exceptions)
        {
            Claim(e.Name, e.NameSpan);
            _exceptions[e.Name] = e;
            for (var k = 0; k < e.Fields.Count; k++) e.Fields[k].Index = k;
            if (e.Fields.Select(f => f.Name).Distinct().Count() != e.Fields.Count)
                diags.Error("TN2004", e.NameSpan, $"field names in '{e.Name}' must be distinct");
        }
    }

    // ---------- exceptions ----------

    /// <summary>.NET exceptions that signal V#'s run-time stops; catching them would turn a stop into control flow.</summary>
    private static readonly Type[] Stops = [typeof(OverflowException), typeof(VSharp.Runtime.ContractViolationException), typeof(OutOfMemoryException), typeof(InsufficientExecutionStackException)];

    private void ResolveExceptions()
    {
        foreach (var e in module.Exceptions)
        {
            if (!e.IsExtern)
            {
                foreach (var f in e.Fields)
                {
                    f.Type = Resolve(f.Type, new HashSet<string>(), new HashSet<string>(), f.Span);
                    if (f.Type.Kind is TK.Unit or TK.Tensor) diags.Error("TN2002", f.Span, $"an exception field cannot have type {f.Type}");
                }
                continue;
            }
            e.Fields.Add(new FieldDecl("message", TType.String, e.NameSpan));
            var type = FindClrType(e.ClrName!);
            if (type == null || !typeof(Exception).IsAssignableFrom(type))
            {
                diags.Error("TN2030", e.NameSpan, type == null ? $".NET type '{e.ClrName}' was not found" : $"'{e.ClrName}' is not an exception type");
                continue;
            }
            if (Stops.FirstOrDefault(type.IsAssignableFrom) is { } stop)
            {
                diags.Error("TN2030", e.NameSpan, $"'{e.ClrName}' cannot be caught in V#, because it would also catch {stop.Name}",
                    "Overflow, contract violations and resource exhaustion are run-time stops, not exceptions. Bind a more specific .NET exception type.");
                continue;
            }
            e.Clr = type;
        }
    }

    private static Type? FindClrType(string name)
    {
        Assembly[] candidates =
        [
            typeof(object).Assembly, typeof(Console).Assembly, typeof(Enumerable).Assembly, typeof(Uri).Assembly,
            .. AppDomain.CurrentDomain.GetAssemblies(),
        ];
        return candidates.Select(a => a.GetType(name)).FirstOrDefault(t => t != null);
    }

    /// <summary>
    /// Decides where an exception thrown at the current point goes: the catch clauses of the enclosing try statements
    /// that may receive it, innermost first, up to one that certainly does. Otherwise it leaves the function, which
    /// must then declare it, unless the callee's 'when' condition can be proved false here (the verifier's job).
    /// </summary>
    private ThrowSite Route(ExceptionDecl e, ThrowsClause? clause, Span span, string what)
    {
        var site = new ThrowSite { Exception = e, Clause = clause };
        for (var i = _tries.Count - 1; i >= 0; i--)
            foreach (var c in _tries[i].Catches.Where(c => c.Decl != null))
            {
                if (!c.Decl!.Overlaps(e)) continue;
                site.Catches.Add(c);
                _reached.Add(c);
                if (c.Decl.Covers(e)) return site;
            }
        site.Escapes = true;
        if (clause?.When == null && !_cur.AllThrows.Any(t => t.Decl != null && t.Decl.Covers(e)))
            diags.Error("TN2030", span, $"{what}, which '{_cur.Name}' neither catches nor declares",
                $"Catch it with try {{ ... }} catch {e.Name} {{ ... }}, or add 'throws {e.Name}' to the contract of '{_cur.Name}'.");
        return site;
    }

    /// <summary>Option[t], from the prelude.</summary>
    private TType OptionOf(TType t) => TType.Named(_types["Option"], [t]);

    private void CheckConsts()
    {
        var earlier = new HashSet<ConstDecl>();
        foreach (var c in module.Consts)
        {
            _cur = new FnDecl { Name = c.Name, NameSpan = c.NameSpan };
            ResetScopes();
            _callSink = [];
            if (c.Type.Kind is TK.Unit or TK.Tensor) diags.Error("TN2025", c.NameSpan, $"a constant cannot have type {c.Type}");
            _earlierConsts = earlier;
            Expect(c.Value, c.Type);
            _earlierConsts = null;
            if (_callSink.Count > 0)
                diags.Error("TN2025", c.Value.Span, $"constant '{c.Name}' calls a function",
                    "A constant is built from literals, earlier constants, operators, constructors and builtins.");
            earlier.Add(c);
        }
    }

    private TType ResolveField(FieldDecl f, TypeDecl t)
    {
        var r = Resolve(f.Type, t.TypeParams.ToHashSet(), new HashSet<string>(), f.Span, allowRefine: true);
        if (r.Kind == TK.Unit) diags.Error("TN2002", f.Span, "a field cannot have type Unit");
        if (r.Kind == TK.Tensor && r.Dims.Any(d => d.Names().Any()))
            diags.Error("TN2009", f.Span, "tensor fields of a type must have literal dimensions");
        return r;
    }

    private bool _fieldsResolved;
    private readonly List<(TType, Span)> _pendingKeys = [];

    /// <summary>Map keys and set elements need run-time equality that agrees with the logic.</summary>
    private void CheckKey(TType t, Span at)
    {
        if (!_fieldsResolved) { _pendingKeys.Add((t, at)); return; }
        if (!t.IsEquatable)
            diags.Error("TN2002", at, $"{t} cannot be a map key or set element",
                "Keys and set elements must be Int, Int32, Bool, String, Date, Decimal, or records and unions of those (no Float, arrays, maps or sets).");
    }

    public TType Resolve(TType t, IReadOnlySet<string> typeParams, IReadOnlySet<string> dimParams, Span at, bool allowRefine = true)
    {
        switch (t.Kind)
        {
            case TK.Array:
                var elem = Resolve(t.Elem!, typeParams, dimParams, at, allowRefine: false);
                if (elem.Kind == TK.Unit) diags.Error("TN2002", at, "Array[Unit] is not a valid type");
                return TType.ArrayOf(elem);
            case TK.Set:
                var item = Resolve(t.Elem!, typeParams, dimParams, at, allowRefine: false);
                CheckKey(item, at);
                return TType.SetOf(item);
            case TK.Map:
                var key = Resolve(t.Key, typeParams, dimParams, at, allowRefine: false);
                var value = Resolve(t.Value, typeParams, dimParams, at, allowRefine: false);
                CheckKey(key, at);
                if (value.Kind == TK.Unit) diags.Error("TN2002", at, "a map value cannot have type Unit");
                return TType.MapOf(key, value);
            case TK.Tensor:
                foreach (var n in t.Dims.SelectMany(d => d.Names()).Distinct().Where(n => !dimParams.Contains(n)))
                    diags.Error("TN2009", at, $"unknown dimension '{n}'",
                        _cur != null ? $"Declare it as a dimension parameter: fn {_cur.Name}[{n}](...)." : null);
                foreach (var d in t.Dims)
                    if (d.Poly().TryGetValue("", out var c) && d.Poly().Count == 1 && c <= 0) diags.Error("TN2009", at, "tensor dimensions must be positive");
                return t;
            case TK.Named when t.Decl == null:
                var span = t.Span.End > 0 ? t.Span : at;
                if (typeParams.Contains(t.Name!))
                {
                    if (t.Args.Count > 0) diags.Error("TN2002", span, $"type parameter '{t.Name}' does not take arguments");
                    return TType.Param(t.Name!);
                }
                if (!_types.TryGetValue(t.Name!, out var decl))
                {
                    diags.Error("TN2001", span, $"unknown type '{t.Name}'",
                        "Types are Int, Int32, Bool, Unit, Float, Decimal, String, Date, Array[T], Map[K, V], Set[T], Tensor[...], the module's own types, and Option[T] and Result[T, E].");
                    return TType.Error;
                }
                if (t.Args.Count != decl.TypeParams.Count)
                {
                    diags.Error("TN2002", span, $"'{decl.Name}' takes {decl.TypeParams.Count} type argument(s) but was given {t.Args.Count}");
                    return TType.Error;
                }
                var args = t.Args.Select(a => Resolve(a, typeParams, dimParams, span, allowRefine: false)).ToList();
                if (decl.Kind != TypeKind.Refinement) return TType.Named(decl, args);
                if (!allowRefine)
                {
                    diags.Error("TN2020", span, $"refinement type '{decl.Name}' cannot be used inside another type",
                        "Refinement types may be used for parameters, results, locals and fields, not as type arguments.");
                    return decl.Base!.Subst(Map(decl.TypeParams, args), new Dictionary<string, Dim>());
                }
                if (decl.Base == null || decl.Base.IsError) return TType.Error;
                return decl.Base.Subst(Map(decl.TypeParams, args), new Dictionary<string, Dim>()).WithRefine(decl, args);
            default:
                return t;
        }
    }

    public static Dictionary<string, TType> Map(IReadOnlyList<string> names, IReadOnlyList<TType> args)
    {
        var m = new Dictionary<string, TType>();
        for (var i = 0; i < names.Count && i < args.Count; i++) m[names[i]] = args[i];
        return m;
    }

    private static void Walk(TType t, Action<string> typeName, Action<Dim> dim)
    {
        switch (t.Kind)
        {
            case TK.Array or TK.Set: Walk(t.Elem!, typeName, dim); break;
            case TK.Map: Walk(t.Key, typeName, dim); Walk(t.Value, typeName, dim); break;
            case TK.Tensor: foreach (var d in t.Dims) dim(d); break;
            case TK.Named:
                if (t.Args.Count == 0) typeName(t.Name!);
                foreach (var a in t.Args) Walk(a, typeName, dim);
                break;
        }
    }

    private void ResolveSignature(FnDecl f)
    {
        _cur = f;
        var inDims = new HashSet<string>();
        var bare = new HashSet<string>();
        var inTypes = new HashSet<string>();
        foreach (var t in f.Params.Select(p => p.Type))
            Walk(t, n => inTypes.Add(n), d => { inDims.UnionWith(d.Names()); if (d.IsBareName) bare.Add(d.Name!); });
        var inRet = new HashSet<string>();
        Walk(f.Ret, n => { inTypes.Add(n); inRet.Add(n); }, d => inDims.UnionWith(d.Names()));

        if (f.Generics.Distinct().Count() != f.Generics.Count) diags.Error("TN2004", f.NameSpan, "type and dimension parameters must be distinct");
        foreach (var g in f.Generics)
        {
            if (inDims.Contains(g) && inTypes.Contains(g))
                diags.Error("TN2009", f.NameSpan, $"'{g}' is used both as a type and as a dimension");
            if (inDims.Contains(g))
            {
                f.DimParams.Add(g);
                if (!bare.Contains(g))
                    diags.Error("TN2009", f.NameSpan, $"dimension parameter '{g}' must appear on its own in a parameter type, so callers can determine it",
                        $"For example: (x: Tensor[{g}, ...]).");
            }
            else
            {
                f.TypeParams.Add(g);
                if (!inTypes.Contains(g)) diags.Error("TN2021", f.NameSpan, $"type parameter '{g}' is not used in the signature");
            }
            if (_global.Contains(g) || Builtins.Contains(g)) diags.Error("TN2004", f.NameSpan, $"the name '{g}' is already used in this module");
        }
        if (f.Kind == FnKind.Extern && f.Generics.Count > 0) diags.Error("TN2017", f.NameSpan, "extern functions cannot be generic");
        if (f.IsMethod && f.Generics.Count > 0) diags.Error("TN2013", f.NameSpan, "a method cannot be generic", "Write a generic module function instead.");
        if (f.IsAsync && f.Generics.Count > 0) diags.Error("TN2013", f.NameSpan, "an async function cannot be generic");
        if (f.IsAbstract && f.Decreases.Count > 0) diags.Error("TN2013", f.Decreases[0].Span, "an interface method has no 'decreases'", "Termination is proved for each implementation.");

        var tps = f.TypeParams.ToHashSet();
        var dps = f.DimParams.ToHashSet();
        foreach (var p in f.Params)
        {
            p.Type = Resolve(p.Type, tps, dps, p.Span);
            if (p.Type.Kind == TK.Unit) diags.Error("TN2002", p.Span, "a parameter cannot have type Unit");
        }
        f.Ret = Resolve(f.Ret, tps, dps, f.NameSpan);
        if (f.Kind == FnKind.Lemma && f.Ret.Kind != TK.Unit) diags.Error("TN2013", f.NameSpan, "a lemma returns Unit");
        if (f.Kind == FnKind.Spec && f.Effects.Count > 0) diags.Error("TN2006", f.NameSpan, "a spec function cannot have effects");
        if (f.Kind == FnKind.Lemma && f.Effects.Count > 0) diags.Error("TN2006", f.NameSpan, "a lemma cannot have effects");
        if (f.Name == "main" && (f.Kind != FnKind.Fn || f.Params.Count > 0 || f.Ret.Kind != TK.Unit || f.Generics.Count > 0))
            diags.Error("TN2013", f.NameSpan, "'main' must be an ordinary function with no parameters that returns Unit");
        if (f.Kind == FnKind.Extern) ResolveExtern(f);
        foreach (var t in f.Throws)
        {
            if (!_exceptions.TryGetValue(t.Name, out var e)) diags.Error("TN2001", t.Span, $"unknown exception '{t.Name}'", "Declare it: exception Name(fields).");
            else if (f.Throws.Count(o => o.Name == t.Name) > 1) diags.Error("TN2004", t.Span, $"'throws {t.Name}' is declared twice", "Combine the conditions: throws E when a || b.");
            else t.Decl = e;
        }
        if (f.IsGhost && f.Throws.Count > 0)
            diags.Error("TN2030", f.Throws[0].Span, $"a {(f.Kind == FnKind.Spec ? "spec function" : "lemma")} cannot throw", "Specifications denote values; they have no exceptional outcome.");
    }

    private static Type? ExternClr(TType t) => t.Kind switch
    {
        TK.Int => typeof(long),
        TK.Int32 => typeof(int),
        TK.Float => typeof(double),
        TK.Bool => typeof(bool),
        TK.String => typeof(string),
        TK.Decimal => typeof(decimal),
        TK.Date => typeof(DateOnly),
        TK.Unit => typeof(void),
        TK.Array => t.Elem!.Kind switch
        {
            TK.Int => typeof(long[]), TK.Int32 => typeof(int[]), TK.Float => typeof(double[]), TK.Bool => typeof(bool[]),
            TK.String => typeof(string[]), TK.Decimal => typeof(decimal[]), _ => null,
        },
        _ => null,
    };

    private void ResolveExtern(FnDecl f)
    {
        var types = f.Params.Select(p => ExternClr(p.Type)).ToList();
        var ret = ExternClr(f.Ret);
        if (f.IsAsync && ret != null) ret = ret == typeof(void) ? typeof(Task) : typeof(Task<>).MakeGenericType(ret);
        if (types.Any(t => t == null) || ret == null)
        {
            diags.Error("TN2017", f.NameSpan, "extern functions may only use Int, Int32, Float, Bool, String, Decimal, Date, Unit and arrays of those");
            return;
        }
        var target = f.ExternTarget!;
        var dot = target.LastIndexOf('.');
        if (dot <= 0)
        {
            diags.Error("TN2017", f.NameSpan, $"'{target}' is not of the form \"Namespace.Type.Method\"");
            return;
        }
        var (typeName, member) = (target[..dot], target[(dot + 1)..]);
        Assembly[] candidates =
        [
            typeof(object).Assembly, typeof(Console).Assembly, typeof(Enumerable).Assembly, typeof(Uri).Assembly,
            .. AppDomain.CurrentDomain.GetAssemblies(),
        ];
        var type = candidates.Select(a => a.GetType(typeName)).FirstOrDefault(t => t != null);
        if (type == null)
        {
            diags.Error("TN2017", f.NameSpan, $".NET type '{typeName}' was not found");
            return;
        }
        var m = type.GetMethod(member, BindingFlags.Public | BindingFlags.Static, types!.ToArray()!)
                ?? (types.Count == 0 ? type.GetProperty(member, BindingFlags.Public | BindingFlags.Static)?.GetMethod : null);
        if (m == null || m.ReturnType != ret)
        {
            var sig = $"static {ret.Name} {member}({string.Join(", ", types.Select(t => t!.Name))})";
            diags.Error("TN2017", f.NameSpan, $"'{typeName}' has no public method or property matching {sig}");
            return;
        }
        f.ExternMethod = m;
    }

    private void CheckRefinement(TypeDecl t)
    {
        _cur = new FnDecl { Name = t.Name, NameSpan = t.NameSpan };
        _cur.TypeParams.AddRange(t.TypeParams);
        ResetScopes();
        _callSink = t.Calls;
        _selfType = t.Base;
        _inSpec = true;
        Expect(t.Pred!, TType.Bool);
        _inSpec = false;
        _selfType = null;
    }

    private void ResetScopes()
    {
        _scopes.Clear();
        _used.Clear();
        _scopes.Add([]);
        _ghost = false;
        _inSpec = false;
    }

    // ---------- functions ----------

    public void CheckFn(FnDecl f)
    {
        _cur = f;
        ResetScopes();
        _callSink = f.Calls;
        foreach (var d in f.DimParams) Declare(d, TType.Int, false, false, VarKind.Dim, f.NameSpan);
        foreach (var p in f.Params) Declare(p.Name, p.Type, false, f.IsGhost, VarKind.Param, p.Span);
        foreach (var t in f.Params.Select(p => p.Type).Append(f.Ret))
            if (t.Refine != null) f.Calls.UnionWith(t.Refine.Calls);

        _inSpec = true;
        foreach (var r in f.Requires) Expect(r, TType.Bool);
        foreach (var t in f.Throws.Where(t => t.When != null)) Expect(t.When!, TType.Bool);
        foreach (var d in f.Decreases) Expect(d, TType.Int);
        _allowResult = true;
        foreach (var e in f.Ensures) Expect(e, TType.Bool);
        _allowResult = false;
        _inSpec = false;

        switch (f.Kind)
        {
            case FnKind.Spec:
                _inSpec = true;
                Expect(f.BodyExpr!, f.Ret);
                _inSpec = false;
                break;
            case FnKind.Lemma:
                _inSpec = true;
                _ghost = true;
                CheckBlock(f.Body, newScope: false);
                _ghost = false;
                _inSpec = false;
                break;
            case FnKind.Fn when f.IsAbstract:
                break;
            case FnKind.Fn or FnKind.Grad:
                CheckBlock(f.Body, newScope: false);
                if (f.Ret.Kind != TK.Unit && !AlwaysReturns(f.Body))
                    diags.Error("TN2010", f.EndSpan, $"function '{f.Name}' can reach its end without returning a {f.Ret}",
                        "Add a 'return' on every path.");
                break;
        }
    }

    private void CheckRecursion()
    {
        var index = new Dictionary<FnDecl, int>();
        var low = new Dictionary<FnDecl, int>();
        var stack = new Stack<FnDecl>();
        var onStack = new HashSet<FnDecl>();
        var next = 0;
        var scc = 0;
        void Visit(FnDecl v)
        {
            index[v] = low[v] = next++;
            stack.Push(v);
            onStack.Add(v);
            foreach (var w in v.Calls)
            {
                if (!index.ContainsKey(w)) { Visit(w); low[v] = Math.Min(low[v], low[w]); }
                else if (onStack.Contains(w)) low[v] = Math.Min(low[v], index[w]);
            }
            if (low[v] != index[v]) return;
            var members = new List<FnDecl>();
            FnDecl x;
            do { x = stack.Pop(); onStack.Remove(x); x.Scc = scc; members.Add(x); } while (x != v);
            scc++;
            var recursive = members.Count > 1 || v.Calls.Contains(v);
            foreach (var m in members) m.Recursive = recursive;
            if (!recursive) return;
            if (members.FirstOrDefault(m => m.IsAbstract) is { } dispatch)
            {
                var at = members.FirstOrDefault(m => !m.IsAbstract) ?? dispatch;
                var others = members.Where(m => !m.IsAbstract).Select(m => $"'{m.Name}'").ToList();
                diags.Error("TN2028", at.NameSpan,
                    $"{string.Join(", ", others)} can call {(others.Count == 1 ? "itself" : "each other")} through interface method '{dispatch.Name}'",
                    "Termination cannot be proved across dynamic dispatch. Recurse with a module function over a union instead, or break the cycle.");
                return;
            }
            foreach (var m in members.Where(m => m.Decreases.Count == 0))
                diags.Error("TN2011", m.NameSpan,
                    members.Count == 1 ? $"recursive function '{m.Name}' needs a 'decreases' clause"
                        : $"'{m.Name}' is mutually recursive with {string.Join(", ", members.Where(o => o != m).Select(o => $"'{o.Name}'"))} and needs a 'decreases' clause",
                    "Add 'decreases <Int expression>' (or 'decreases a, b' for a lexicographic measure) that gets smaller on every recursive call.");
            var lengths = members.Where(m => m.Decreases.Count > 0).Select(m => m.Decreases.Count).Distinct().ToList();
            if (lengths.Count > 1)
                diags.Error("TN2012", v.NameSpan,
                    $"mutually recursive functions {string.Join(", ", members.Select(m => $"'{m.Name}'"))} must use 'decreases' measures of the same length");
        }
        foreach (var f in module.Fns) if (!index.ContainsKey(f)) Visit(f);
    }

    private static bool AlwaysReturns(List<Stmt> stmts) => stmts.Any(s => s switch
    {
        Return or Throw => true,
        Try t => AlwaysReturns(t.Body) && t.Catches.All(c => AlwaysReturns(c.Body)),
        If { Else: not null } i => AlwaysReturns(i.Then) && AlwaysReturns(i.Else),
        MatchStmt m => m.Arms.All(a => AlwaysReturns(a.Body)),
        _ => false,
    });

    // ---------- scopes ----------

    private void Declare(string name, TType type, bool mutable, bool ghost, VarKind kind, Span span)
    {
        if (!_used.Add(name) || CoreBuiltins.Contains(name) || _global.Contains(name))
            diags.Error("TN2004", span, $"the name '{name}' is already used in this function or module",
                "Names are unique within a function: shadowing and redeclaration are not allowed.");
        _scopes[^1][name] = new VarInfo(type, mutable, ghost, kind);
    }

    private VarInfo? Lookup(string name)
    {
        for (var i = _scopes.Count - 1; i >= 0; i--)
            if (_scopes[i].TryGetValue(name, out var v)) return v;
        return null;
    }

    private IReadOnlySet<string> DimSet => _cur.DimParams.ToHashSet();
    private IReadOnlySet<string> TypeSet => _cur.TypeParams.ToHashSet();

    // ---------- statements ----------

    private void CheckBlock(List<Stmt> stmts, bool newScope = true)
    {
        if (newScope) _scopes.Add([]);
        foreach (var s in stmts) CheckStmt(s);
        if (newScope) _scopes.RemoveAt(_scopes.Count - 1);
    }

    /// <summary>Checks an expression in the current statement context: specification rules apply in ghost code.</summary>
    private void Code(Expr e, TType want)
    {
        var saved = _inSpec;
        _inSpec = _ghost;
        Expect(e, want);
        _inSpec = saved;
    }

    private TType CodeInfer(Expr e)
    {
        var saved = _inSpec;
        _inSpec = _ghost;
        var t = C(e);
        _inSpec = saved;
        return t;
    }

    private void Spec(Expr e, TType want)
    {
        var saved = _inSpec;
        _inSpec = true;
        Expect(e, want);
        _inSpec = saved;
    }

    private void CheckStmt(Stmt s)
    {
        s.Ghost |= _ghost;
        switch (s)
        {
            case Let l:
            {
                var ghost = _ghost || l.Ghost;
                l.Ghost = ghost;
                if (l.Annotation != null) l.Annotation = Resolve(l.Annotation, TypeSet, DimSet, l.Span);
                var savedSpec = _inSpec;
                _inSpec = ghost;
                TType t;
                if (l.Annotation != null) { Expect(l.Init, l.Annotation); t = l.Annotation; }
                else t = C(l.Init);
                _inSpec = savedSpec;
                if (t.Kind == TK.Unit) diags.Error("TN2002", l.Span, "a variable cannot have type Unit");
                l.VarType = t;
                Declare(l.Name, t, l.Mutable, ghost, VarKind.Local, l.Span);
                break;
            }
            case Set st:
            {
                var v = Lookup(st.Name);
                if (v == null) { diags.Error("TN2001", st.Span, $"unknown variable '{st.Name}'"); CodeInfer(st.Value); break; }
                if (!v.Mutable)
                    diags.Error("TN2005", st.Span, $"'{st.Name}' is immutable", $"Declare it with 'var {st.Name} = ...' to allow 'set'.");
                if (_ghost && !v.Ghost)
                    diags.Error("TN2018", st.Span, $"ghost code cannot assign the non-ghost variable '{st.Name}'");
                st.Ghost = v.Ghost;
                st.VarType = v.Type;
                if (v.Ghost) Spec(st.Value, v.Type);
                else Code(st.Value, v.Type);
                break;
            }
            case If i:
                Code(i.Cond, TType.Bool);
                CheckBlock(i.Then);
                if (i.Else != null) CheckBlock(i.Else);
                break;
            case While w:
                Code(w.Cond, TType.Bool);
                foreach (var inv in w.Invariants) Spec(inv, TType.Bool);
                foreach (var d in w.Decreases) Spec(d, TType.Int);
                if (w.Decreases.Count == 0)
                    diags.Error("TN2011", w.Span, "a 'while' loop needs a 'decreases' clause",
                        "Add 'decreases <Int expression>' that is non-negative while the loop runs and gets smaller on every iteration.");
                _loops++;
                CheckBlock(w.Body);
                _loops--;
                break;
            case For fr:
            {
                if (fr.Source != null)
                {
                    var src = CodeInfer(fr.Source);
                    if (!src.IsError && src.Kind != TK.Array) diags.Error("TN2002", fr.Source.Span, $"'for ... in' iterates an array or a range 'lo..hi', not {src}");
                    fr.ElemType = src.Kind == TK.Array ? src.Elem! : TType.Error;
                }
                else
                {
                    Code(fr.Lo!, TType.Int);
                    Code(fr.Hi!, TType.Int);
                }
                _scopes.Add([]);
                // Loop variables are scoped to the loop, like quantifier variables, so loops can reuse 'i' and 'x'.
                void LoopVar(string name, TType type)
                {
                    if (Lookup(name) != null || _global.Contains(name) || CoreBuiltins.Contains(name))
                        diags.Error("TN2004", fr.Span, $"loop variable '{name}' shadows another name", "Pick a name not already in scope.");
                    _scopes[^1][name] = new VarInfo(type, false, _ghost, VarKind.Local);
                }
                LoopVar(fr.IndexName, TType.Int);
                if (fr.Elem != null) LoopVar(fr.Elem, fr.ElemType);
                foreach (var inv in fr.Invariants) Spec(inv, TType.Bool);
                _loops++;
                CheckBlock(fr.Body);
                _loops--;
                _scopes.RemoveAt(_scopes.Count - 1);
                break;
            }
            case Break or Continue:
                if (_loops == 0)
                    diags.Error("TN2024", s.Span, $"'{(s is Break ? "break" : "continue")}' is only allowed inside a loop");
                break;
            case MatchStmt m:
            {
                var st = CodeInfer(m.Scrutinee);
                var arms = m.Arms.Select(a => a.Pattern).ToList();
                CheckPatterns(st, arms, m.Span);
                foreach (var (p, body) in m.Arms)
                {
                    _scopes.Add([]);
                    BindPattern(p, st);
                    CheckBlock(body, newScope: false);
                    _scopes.RemoveAt(_scopes.Count - 1);
                }
                break;
            }
            case Return r:
                if (_ghost) diags.Error("TN2018", r.Span, "'return' is not allowed in ghost code");
                Code(r.Value, _cur.Ret);
                break;
            case Assert a:
                Spec(a.Cond, TType.Bool);
                break;
            case Print p:
                if (_ghost) diags.Error("TN2018", p.Span, "'print' is not allowed in ghost code");
                else if (!_cur.Effects.Contains("io"))
                    diags.Error("TN2006", p.Span, $"'print' needs the io effect, but '{_cur.Name}' does not declare it",
                        $"Declare the effect on the function: fn {_cur.Name}(...) -> ... effects io");
                if (CodeInfer(p.Value).Kind == TK.Unit) diags.Error("TN2002", p.Span, "cannot print a Unit value");
                break;
            case Do d:
                if (d.Call is not Call c) { diags.Error("TN2013", d.Span, "'do' must be followed by a function call"); CodeInfer(d.Call); break; }
                _inDo = true;
                var lemma = _fns.TryGetValue(c.Name, out var target) && target.Kind == FnKind.Lemma;
                d.Ghost = _ghost || lemma;
                var saved = _inSpec;
                _inSpec = d.Ghost;
                C(c);
                _inSpec = saved;
                _inDo = false;
                break;
            case Throw th:
                CheckThrow(th);
                break;
            case Try t:
                CheckTry(t);
                break;
        }
    }

    private void CheckThrow(Throw th)
    {
        var c = th.Value;
        if (_ghost) diags.Error("TN2018", th.Span, "'throw' is not allowed in ghost code");
        if (!_exceptions.TryGetValue(c.Name, out var e))
        {
            diags.Error("TN2001", c.Span, $"unknown exception '{c.Name}'", "Declare it: exception Name(fields).");
            foreach (var a in c.Args) CodeInfer(a);
            return;
        }
        c.Exception = e;
        c.Type = TType.Unit;
        var ps = e.Fields.Select(f => (f.Name, f.Type)).ToList();
        if (c.Args.Count != ps.Count)
        {
            diags.Error("TN2007", c.Span, $"exception '{e.Name}' has {ps.Count} field(s) but was given {c.Args.Count}");
            foreach (var a in c.Args) CodeInfer(a);
            return;
        }
        CheckArgNames(c, ps);
        for (var i = 0; i < ps.Count; i++) Code(c.Args[i], ps[i].Type);
        if (e.Clr != null && e.Clr.GetConstructor([typeof(string)]) == null)
            diags.Error("TN2030", c.Span, $"'{e.ClrName}' has no public constructor taking a message, so V# cannot throw it");
        th.Site = Route(e, null, th.Span, $"'{e.Name}' is thrown here");
    }

    private void CheckTry(Try t)
    {
        if (_ghost) diags.Error("TN2018", t.Span, "'try' is not allowed in ghost code");
        foreach (var c in t.Catches)
        {
            if (_exceptions.TryGetValue(c.Name, out var e)) c.Decl = e;
            else diags.Error("TN2001", c.Span, $"unknown exception '{c.Name}'");
        }
        for (var j = 1; j < t.Catches.Count; j++)
            if (t.Catches.Take(j).FirstOrDefault(c => c.Decl != null && t.Catches[j].Decl != null && c.Decl.Covers(t.Catches[j].Decl!)) is { } earlier)
                diags.Error("TN2030", t.Catches[j].Span, $"this catch can never run: the earlier 'catch {earlier.Name}' already catches '{t.Catches[j].Name}'",
                    "List the more specific exception first.");
        _tries.Add(t);
        CheckBlock(t.Body);
        _tries.RemoveAt(_tries.Count - 1);
        foreach (var c in t.Catches)
        {
            _scopes.Add([]);
            if (c.Decl != null)
            {
                if (!_reached.Contains(c))
                    diags.Error("TN2030", c.Span, $"nothing in the try block can throw '{c.Name}'",
                        $"Only 'throw' statements and calls to functions that declare 'throws {c.Name}' (or a related .NET exception) can throw it.");
                if (c.Binders.Count > 0 && c.Binders.Count != c.Decl.Fields.Count)
                    diags.Error("TN2007", c.Span, $"exception '{c.Name}' has {c.Decl.Fields.Count} field(s) but the catch names {c.Binders.Count}",
                        c.Decl.Fields.Count > 0 ? $"Its fields are: {string.Join(", ", c.Decl.Fields.Select(f => f.Name))}." : $"Write: catch {c.Name} {{ ... }}");
                else
                    for (var k = 0; k < c.Binders.Count; k++)
                        if (c.Binders[k] != "_") Declare(c.Binders[k], c.Decl.Fields[k].Type, false, false, VarKind.Local, c.Span);
            }
            CheckBlock(c.Body, newScope: false);
            _scopes.RemoveAt(_scopes.Count - 1);
        }
    }

    private void CheckPatterns(TType scrutinee, List<Pattern> patterns, Span span)
    {
        if (scrutinee.IsError) return;
        if (scrutinee.Kind is TK.Int or TK.Int32 or TK.Bool or TK.String or TK.Decimal)
        {
            CheckLiteralPatterns(scrutinee, patterns, span);
            return;
        }
        if (scrutinee.Kind != TK.Named || scrutinee.Decl!.Kind != TypeKind.Union)
        {
            diags.Error("TN2016", span, $"'match' needs a union value or an Int, Int32, Bool, String or Decimal value, but found {scrutinee}");
            return;
        }
        var union = scrutinee.Decl;
        var seen = new HashSet<string>();
        var wildcard = false;
        void Case(Pattern p, bool alternative)
        {
            if (p.Literal != null || p.Alternatives != null || p.Case == null)
            {
                diags.Error("TN2016", p.Span, alternative ? "alternatives in a union 'match' must be case names" : "a union 'match' needs case patterns");
                return;
            }
            if (!_cases.TryGetValue(p.Case, out var c) || c.Owner != union)
            {
                diags.Error("TN2016", p.Span, $"'{p.Case}' is not a case of {union.Name}",
                    $"The cases are: {string.Join(", ", union.Cases.Select(x => x.Name))}.");
                return;
            }
            p.Resolved = c;
            if (!seen.Add(c.Name)) diags.Error("TN2016", p.Span, $"case '{c.Name}' is matched twice");
            if (alternative)
            {
                if (p.Binders.Any(b => b != "_"))
                    diags.Error("TN2016", p.Span, "the alternatives of an or-pattern cannot bind names", $"Write just '{c.Name}', or give it an arm of its own.");
            }
            else if (p.Binders.Count != c.Fields.Count)
                diags.Error("TN2016", p.Span, $"case '{c.Name}' has {c.Fields.Count} field(s) but the pattern binds {p.Binders.Count}",
                    c.Fields.Count == 0 ? $"Write '{c.Name}' with no parentheses." : $"Write {c.Name}({string.Join(", ", c.Fields.Select(f => f.Name))}).");
        }
        foreach (var p in patterns)
        {
            if (wildcard) diags.Error("TN2016", p.Span, "this arm is unreachable: an earlier '_' arm matches everything");
            if (p.IsWildcard) { wildcard = true; continue; }
            if (p.Alternatives != null) foreach (var a in p.Alternatives) Case(a, alternative: true);
            else Case(p, alternative: false);
        }
        var missing = union.Cases.Where(c => !seen.Contains(c.Name)).Select(c => c.Name).ToList();
        if (!wildcard && missing.Count > 0)
            diags.Error("TN2016", span, $"'match' is not exhaustive: missing {string.Join(", ", missing)}", "Add an arm for each missing case, or a final '_' arm.");
    }

    private void CheckLiteralPatterns(TType scrutinee, List<Pattern> patterns, Span span)
    {
        var seen = new HashSet<string>();
        var wildcard = false;
        void Literal(Pattern p)
        {
            if (p.Literal == null)
            {
                diags.Error("TN2016", p.Span, $"a 'match' on {scrutinee} needs literal patterns or '_'",
                    p.Case != null ? $"'{p.Case}' is a name; a pattern on {scrutinee} must be a literal value." : null);
                return;
            }
            var saved = _inSpec;
            _inSpec = true;
            Expect(p.Literal, scrutinee.Base);
            _inSpec = saved;
            var key = LiteralKey(p.Literal);
            if (key != null && !seen.Add(key)) diags.Error("TN2016", p.Span, $"the value {key} is matched twice");
        }
        foreach (var p in patterns)
        {
            if (wildcard) diags.Error("TN2016", p.Span, "this arm is unreachable: an earlier '_' arm matches everything");
            if (p.IsWildcard) { wildcard = true; continue; }
            if (p.Alternatives != null) foreach (var a in p.Alternatives) Literal(a);
            else Literal(p);
        }
        var complete = scrutinee.Kind == TK.Bool && seen.Contains("true") && seen.Contains("false");
        if (!wildcard && !complete)
            diags.Error("TN2016", span, $"'match' on {scrutinee} is not exhaustive", "Add a final '_' arm for the values not listed.");
    }

    /// <summary>A canonical text for a literal pattern, to find duplicates.</summary>
    private static string? LiteralKey(Expr e) => e switch
    {
        IntLit i => i.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Unary { Op: "-", Operand: IntLit i } => (-i.Value).ToString(System.Globalization.CultureInfo.InvariantCulture),
        DecLit d => d.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Unary { Op: "-", Operand: DecLit d } => (-d.Value).ToString(System.Globalization.CultureInfo.InvariantCulture),
        StrLit s => "\"" + s.Value + "\"",
        BoolLit b => b.Value ? "true" : "false",
        _ => null,
    };

    private void BindPattern(Pattern p, TType scrutinee, bool bound = false)
    {
        if (p.Resolved == null || p.Alternatives != null || p.Binders.Count != p.Resolved.Fields.Count) return;
        var map = Map(p.Resolved.Owner.TypeParams, scrutinee.Args);
        for (var k = 0; k < p.Binders.Count; k++)
        {
            var (name, type) = (p.Binders[k], p.Resolved.Fields[k].Type.Subst(map, new Dictionary<string, Dim>()));
            if (name == "_") continue;
            if (!bound) { Declare(name, type, false, _ghost || _inSpec, VarKind.Local, p.Span); continue; }
            // Like quantifier variables, pattern variables in a specification are scoped to their arm.
            if (Lookup(name) != null || _global.Contains(name) || CoreBuiltins.Contains(name))
                diags.Error("TN2004", p.Span, $"pattern variable '{name}' shadows another name", "Pick a name not already in scope.");
            _scopes[^1][name] = new VarInfo(type, false, true, VarKind.Local);
        }
    }

    // ---------- expressions ----------

    private void Expect(Expr e, TType want)
    {
        C(e, want);
        Mismatch(e, want);
    }

    private void Mismatch(Expr e, TType want)
    {
        if (want.IsError || e.Type.IsError) return;
        var inst = new Inst([], []);
        if (Unify(want, e.Type, inst))
        {
            foreach (var (a, b, _) in inst.Pending)
                if (!ShapeEq(e, a, b)) { ReportMismatch(e, want, "shape mismatch"); return; }
            return;
        }
        if (Coerce(e, want)) return;
        ReportMismatch(e, want, want.Kind == TK.Tensor && e.Type.Kind == TK.Tensor ? "shape mismatch" : "type mismatch");
    }

    private void ReportMismatch(Expr e, TType want, string what) =>
        diags.Error(what == "shape mismatch" ? "TN2003" : "TN2002", e.Span, $"{what}: expected {want} but found {e.Type}");

    /// <summary>Records a dimension equality on <paramref name="at"/>. False when the two are different constants.</summary>
    private static bool ShapeEq(Expr at, Dim a, Dim b)
    {
        if (a.PolyEquals(b)) return true;
        if (!a.Names().Any() && !b.Names().Any()) return false;
        at.ShapeEqs.Add((a, b));
        return true;
    }

    private sealed class Inst(HashSet<string> typeVars, HashSet<string> dimVars)
    {
        public HashSet<string> TypeVars { get; } = typeVars;
        public HashSet<string> DimVars { get; } = dimVars;
        public Dictionary<string, TType> Types { get; } = [];
        public Dictionary<string, Dim> Dims { get; } = [];
        public List<(Dim P, Dim A, int Arg)> Pending { get; } = [];
        public int Arg { get; set; }
    }

    private static bool Unify(TType p, TType a, Inst inst)
    {
        if (p.IsError || a.IsError) return true;
        if (p.Kind == TK.Param && inst.TypeVars.Contains(p.Name!))
        {
            if (inst.Types.TryGetValue(p.Name!, out var bound)) return bound.Same(a);
            inst.Types[p.Name!] = a.Base;
            return true;
        }
        if (p.Kind != a.Kind) return false;
        switch (p.Kind)
        {
            case TK.Array: return Unify(p.Elem!, a.Elem!, inst);
            case TK.Tensor:
                if (p.ElemType != a.ElemType || p.Dims.Count != a.Dims.Count) return false;
                for (var k = 0; k < p.Dims.Count; k++)
                {
                    var pd = p.Dims[k];
                    if (pd.IsBareName && inst.DimVars.Contains(pd.Name!) && !inst.Dims.ContainsKey(pd.Name!)) inst.Dims[pd.Name!] = a.Dims[k];
                    else inst.Pending.Add((pd, a.Dims[k], inst.Arg));
                }
                return true;
            case TK.Named:
                return p.Name == a.Name && p.Args.Count == a.Args.Count && p.Args.Zip(a.Args).All(x => Unify(x.First, x.Second, inst));
            case TK.Param: return p.Name == a.Name;
            default: return true;
        }
    }

    private TType C(Expr e, TType? expected = null)
    {
        e.Type = Infer(e, expected);
        e.RealModel = e switch
        {
            Var { Kind: VarKind.Elem } => true,
            Call { Name: "row_sum", IsBuiltin: true } => true,
            Unary u => u.Operand.RealModel,
            Binary b when b.Op is "+" or "-" or "*" or "/" => b.Left.RealModel || b.Right.RealModel,
            _ => false,
        };
        return e.Type;
    }

    private TType Infer(Expr e, TType? expected)
    {
        switch (e)
        {
            case IntLit il:
                // An integer literal takes the Int32 or Decimal type its context expects.
                if (expected?.Kind == TK.Int32 && il.Value is >= int.MinValue and <= int.MaxValue) return TType.Int32;
                if (expected?.Kind == TK.Decimal) return TType.Decimal;
                return TType.Int;
            case FloatLit: return TType.Float;
            case DecLit: return TType.Decimal;
            case StrLit: return TType.String;
            case BoolLit: return TType.Bool;
            case UnitLit: return TType.Unit;
            case Interp ip:
                foreach (var part in ip.Parts.Where(p => p is not StrLit))
                {
                    var pt = C(part);
                    if (!pt.IsError && pt.Kind is not (TK.String or TK.Int or TK.Int32 or TK.Bool or TK.Decimal or TK.Date))
                        diags.Error("TN2002", part.Span, $"cannot interpolate a {pt} into a string",
                            "Interpolate String, Int, Int32, Bool, Decimal or Date values; format other values field by field.");
                }
                return TType.String;
            case Lambda lam:
                diags.Error("TN2023", lam.Span, "a lambda can only be an argument of a collection builtin such as map, filter or sort_by",
                    "Lambdas are inlined where they are written; they are not values.");
                return TType.Error;
            case WithExpr w: return InferWith(w);
            case Hole h:
                module.Holes.Add(h);
                return expected ?? TType.Error;
            case Var v: return InferVar(v, expected);
            case Unary u:
                if (u.Op == "!") { Expect(u.Operand, TType.Bool); return TType.Bool; }
                var ut = C(u.Operand, expected);
                if (ut.IsError) return TType.Int;
                if (!ut.IsNumeric) { diags.Error("TN2002", u.Span, $"'-' needs a number but found {ut}"); return TType.Int; }
                return ut.Base;
            case Binary b: return InferBinary(b);
            case IfExpr i:
            {
                Expect(i.Cond, TType.Bool);
                if (expected is { IsInterface: true })
                {
                    Expect(i.Then, expected);
                    Expect(i.Else, expected);
                    return expected;
                }
                var tt = C(i.Then, expected);
                Expect(i.Else, tt.IsError ? expected ?? tt : tt);
                return tt.IsError ? i.Else.Type : tt;
            }
            case Index ix:
            {
                var at = C(ix.Array);
                Expect(ix.At, TType.Int);
                if (at.IsError) return at;
                if (at.Kind != TK.Array) { diags.Error("TN2002", ix.Span, $"only arrays can be indexed, not {at}"); return TType.Error; }
                return at.Elem!;
            }
            case FieldAccess fa:
            {
                var tt = C(fa.Target);
                if (tt.IsError) return tt;
                if (tt.Kind != TK.Named || tt.Decl!.Kind != TypeKind.Record)
                {
                    diags.Error("TN2002", fa.Span, $"'.{fa.Field}' needs a record but found {tt}",
                        tt.Kind == TK.Named && tt.Decl!.Kind == TypeKind.Union ? "Use 'match' to read the fields of a union case." : null);
                    return TType.Error;
                }
                var field = tt.Decl.Fields.FirstOrDefault(f => f.Name == fa.Field);
                if (field == null)
                {
                    diags.Error("TN2001", fa.Span, $"'{tt.Decl.Name}' has no field '{fa.Field}'",
                        $"The fields are: {string.Join(", ", tt.Decl.Fields.Select(f => f.Name))}.");
                    return TType.Error;
                }
                fa.Resolved = field;
                return field.Type.Subst(Map(tt.Decl.TypeParams, tt.Args), new Dictionary<string, Dim>());
            }
            case ArrayLit a:
            {
                var elem = expected?.Kind == TK.Array ? expected.Elem : null;
                foreach (var el in a.Elems)
                {
                    if (elem == null) elem = C(el);
                    else Expect(el, elem);
                }
                if (elem == null) { diags.Error("TN2021", a.Span, "cannot infer the element type of an empty array", "Annotate it: let xs: Array[Int] = []"); return TType.Error; }
                if (elem.Kind == TK.Unit) diags.Error("TN2002", a.Span, "Array[Unit] is not a valid type");
                return TType.ArrayOf(elem.Base);
            }
            case TensorLit t:
            {
                long n = 1;
                foreach (var d in t.Shape)
                {
                    if (d <= 0) { diags.Error("TN2009", t.Span, "tensor dimensions must be positive"); return TType.Error; }
                    n *= d;
                }
                if (n != t.Values.Count)
                    diags.Error("TN2003", t.Span, $"tensor literal of shape [{string.Join(", ", t.Shape)}] needs {n} values but has {t.Values.Count}");
                return TType.Tensor(t.Elem, t.Shape.Select(Dim.Of).ToList());
            }
            case Quant q: return InferQuant(q);
            case MatchExpr m:
            {
                var st = C(m.Scrutinee);
                CheckPatterns(st, m.Arms.Select(a => a.Pattern).ToList(), m.Span);
                TType? result = expected;
                foreach (var (p, body) in m.Arms)
                {
                    _scopes.Add([]);
                    BindPattern(p, st, bound: _inSpec);
                    if (result == null || result.IsError) result = C(body);
                    else Expect(body, result);
                    _scopes.RemoveAt(_scopes.Count - 1);
                }
                return result ?? TType.Error;
            }
            case Call c: return InferCall(c, expected);
            default: throw new InvalidOperationException(e.GetType().Name);
        }
    }

    private TType InferVar(Var v, TType? expected)
    {
        if (v.Name == "result")
        {
            if (!_allowResult) { diags.Error("TN2008", v.Span, "'result' can only be used in an 'ensures' clause"); return TType.Error; }
            v.Kind = VarKind.Result;
            return _cur.Ret;
        }
        if (v.Name == "self" && Lookup("self") == null)
        {
            if (_selfType == null) { diags.Error("TN2008", v.Span, "'self' can only be used in a method, a class invariant or the 'where' clause of a refinement type"); return TType.Error; }
            v.Kind = VarKind.Self;
            return _selfType;
        }
        var found = Lookup(v.Name);
        if (found != null)
        {
            if (found.Ghost && !_inSpec)
                diags.Error("TN2018", v.Span, $"'{v.Name}' is ghost and cannot be used in executable code",
                    "Ghost variables and the parameters of spec functions and lemmas exist only for the proof.");
            v.Kind = found.Kind;
            return found.Type;
        }
        if (_consts.TryGetValue(v.Name, out var k))
        {
            if (_earlierConsts != null && !_earlierConsts.Contains(k))
                diags.Error("TN2025", v.Span, $"constant '{k.Name}' is used before it is declared, or by itself", "A constant can only use the constants declared above it.");
            v.Kind = VarKind.Const;
            v.Const = k;
            return k.Type;
        }
        if (_cases.TryGetValue(v.Name, out var c))
        {
            if (c.Fields.Count > 0)
            {
                diags.Error("TN2007", v.Span, $"case '{c.Name}' needs {c.Fields.Count} argument(s)", $"Write {c.Name}({string.Join(", ", c.Fields.Select(f => f.Name + ": ..."))}).");
                return TType.Error;
            }
            v.Kind = VarKind.Ctor;
            v.Ctor = c;
            if (c.Owner.TypeParams.Count == 0) return TType.Named(c.Owner, []);
            if (expected is { Kind: TK.Named } && expected.Decl == c.Owner)
            {
                v.TypeArgs = Map(c.Owner.TypeParams, expected.Args);
                return expected.Base;
            }
            diags.Error("TN2021", v.Span, $"cannot infer the type arguments of '{c.Name}'",
                $"Annotate the variable it is assigned to, for example: let x: {c.Owner.Name}[Int] = {c.Name}");
            return TType.Error;
        }
        if (_fns.ContainsKey(v.Name)) diags.Error("TN2001", v.Span, $"'{v.Name}' is a function; call it with parentheses");
        else diags.Error("TN2001", v.Span, $"unknown variable '{v.Name}'");
        return TType.Error;
    }

    private static bool IsNumLiteral(Expr e) => e is IntLit or Unary { Op: "-", Operand: IntLit };

    /// <summary>Types both operands of a binary operator alike; an integer literal on the left takes the right operand's type.</summary>
    private TType Operands(Binary b)
    {
        if (IsNumLiteral(b.Left) && !IsNumLiteral(b.Right))
        {
            var rt = C(b.Right);
            if (rt.IsError) { C(b.Left); return rt; }
            Expect(b.Left, rt.Base);
            return rt;
        }
        var lt = C(b.Left);
        if (lt.IsError) { C(b.Right); return lt; }
        Expect(b.Right, lt.Base);
        return lt;
    }

    private TType InferWith(WithExpr w)
    {
        var tt = C(w.Target);
        if (tt.IsError) { foreach (var (_, v) in w.Updates) C(v); return tt; }
        if (tt.Kind != TK.Named || tt.Decl!.Kind != TypeKind.Record)
        {
            diags.Error("TN2002", w.Target.Span, $"'with' needs a record but found {tt}");
            foreach (var (_, v) in w.Updates) C(v);
            return TType.Error;
        }
        var map = Map(tt.Decl.TypeParams, tt.Args);
        var seen = new HashSet<string>();
        foreach (var (name, value) in w.Updates)
        {
            var field = tt.Decl.Fields.FirstOrDefault(f => f.Name == name);
            w.Resolved.Add(field);
            if (field == null)
            {
                diags.Error("TN2001", value.Span, $"'{tt.Decl.Name}' has no field '{name}'", $"The fields are: {string.Join(", ", tt.Decl.Fields.Select(f => f.Name))}.");
                C(value);
                continue;
            }
            if (!seen.Add(name)) diags.Error("TN2004", value.Span, $"field '{name}' is updated twice");
            Expect(value, field.Type.Subst(map, new Dictionary<string, Dim>()));
        }
        return tt.Base;
    }

    private TType InferBinary(Binary b)
    {
        switch (b.Op)
        {
            case "+" or "-" or "*" or "/":
            {
                var lt = Operands(b);
                if (lt.IsError) return TType.Int;
                if (b.Op == "+" && lt.Kind == TK.String) return TType.String;
                if (!lt.IsNumeric)
                {
                    diags.Error("TN2002", b.Left.Span, $"'{b.Op}' needs numbers{(b.Op == "+" ? " or strings" : "")} but found {lt}");
                    return TType.Int;
                }
                return lt.Base;
            }
            case "%":
            {
                var lt = Operands(b);
                if (!lt.IsError && !lt.IsIntegral) diags.Error("TN2002", b.Left.Span, $"'%' needs Int or Int32 operands but found {lt}");
                return lt.IsIntegral ? lt.Base : TType.Int;
            }
            case "<" or "<=" or ">" or ">=":
            {
                var lt = Operands(b);
                if (!lt.IsError && !lt.IsOrdered) diags.Error("TN2002", b.Left.Span, $"'{b.Op}' compares numbers or dates, not {lt}");
                return TType.Bool;
            }
            case "==" or "!=":
            {
                var lt = Operands(b);
                // In specifications, records, unions and type parameters compare structurally; arrays and tensors
                // are excluded because their solver model does not have run-time equality. Executable code compares
                // the types whose Equals agrees with that structural equality.
                var structural = _inSpec && lt.Kind is TK.Named or TK.Param && !lt.Contains(t => t.Kind is TK.Array or TK.Tensor);
                var executable = lt.Kind is TK.Float || lt.IsEquatable && lt.Kind != TK.Param;
                if (!executable && !structural)
                    diags.Error("TN2002", b.Span, $"'{b.Op}' cannot compare {lt} values{(_inSpec ? "" : " in executable code")}",
                        lt.IsInterface ? "Interface values have no equality in code: two implementations may define it differently. Compare what their methods return."
                        : lt.Kind is TK.Named or TK.Param
                            ? "Code can compare records, classes and unions without Float, array, map, set or interface fields. Use 'match' to inspect a union, or compare fields."
                            : "Compare elements or sizes instead.");
                return TType.Bool;
            }
            default:
                Expect(b.Left, TType.Bool); Expect(b.Right, TType.Bool);
                return TType.Bool;
        }
    }

    private TType InferQuant(Quant q)
    {
        if (!_inSpec)
        {
            diags.Error("TN2008", q.Span, "quantifiers are specification-only",
                "Use 'forall'/'exists' in requires, ensures, invariant, assert or ghost code; use a loop in executable code.");
            // Check the rest as a specification, so the one mistake is reported once.
            _inSpec = true;
            var t = InferQuant(q);
            _inSpec = false;
            return t;
        }
        if (q.Kind == QuantKind.Range) { Expect(q.Lo!, TType.Int); Expect(q.Hi!, TType.Int); }
        if (q.Kind == QuantKind.Elems)
        {
            var st = C(q.Source!);
            if (!st.IsError && st.Kind != TK.Tensor) diags.Error("TN2002", q.Source!.Span, $"'elems' needs a tensor but found {st}");
        }
        _scopes.Add([]);
        for (var i = 0; i < q.Binders.Count; i++)
        {
            var (name, type) = q.Binders[i];
            if (q.Kind == QuantKind.Typed) q.Binders[i] = (name, type = Resolve(type, TypeSet, DimSet, q.Span));
            if (Lookup(name) != null || _global.Contains(name) || q.Binders.Take(i).Any(o => o.Name == name))
                diags.Error("TN2004", q.Span, $"bound variable '{name}' shadows another name", "Pick a name not already in scope.");
            _scopes[^1][name] = new VarInfo(type, false, true, q.Kind == QuantKind.Elems ? VarKind.Elem : VarKind.Bound);
        }
        if (q.Kind == QuantKind.Typed)
        {
            if (q.Triggers.Count == 0)
                diags.Error("TN2019", q.Span, "a quantifier over a type needs at least one 'trigger'",
                    $"Add 'trigger f({q.Binders[0].Name})' naming a term that every useful instance mentions.");
            foreach (var group in q.Triggers)
            {
                foreach (var t in group)
                {
                    C(t);
                    if (t is not (Index or Call { IsBuiltin: false } or FieldAccess))
                        diags.Error("TN2019", t.Span, "a trigger must be a function call, an array index or a field access");
                }
                var mentioned = new HashSet<string>();
                foreach (var t in group) CollectVars(t, mentioned);
                foreach (var (name, _) in q.Binders.Where(b => !mentioned.Contains(b.Name)))
                    diags.Error("TN2019", group[0].Span, $"trigger does not mention bound variable '{name}'", "Every trigger must mention every bound variable.");
            }
        }
        Expect(q.Body, TType.Bool);
        _scopes.RemoveAt(_scopes.Count - 1);
        return TType.Bool;
    }

    private static void CollectVars(Expr e, HashSet<string> into)
    {
        switch (e)
        {
            case Var v: into.Add(v.Name); break;
            case Call c: foreach (var a in c.Args) CollectVars(a, into); break;
            case Index i: CollectVars(i.Array, into); CollectVars(i.At, into); break;
            case FieldAccess f: CollectVars(f.Target, into); break;
            case Binary b: CollectVars(b.Left, into); CollectVars(b.Right, into); break;
            case Unary u: CollectVars(u.Operand, into); break;
        }
    }

    // ---------- calls ----------

    private TType InferCall(Call c, TType? expected)
    {
        var lemmaCall = _inDo;
        _inDo = false;
        if (c.Method) return InferMethodCall(c);
        if (c.Awaited && (Builtins.Contains(c.Name) || _cases.ContainsKey(c.Name) || _types.ContainsKey(c.Name)))
            diags.Error("TN2029", c.Span, $"'{c.Name}' is not an async function, so it cannot be awaited", "Remove 'await'.");
        if (Builtins.Contains(c.Name))
        {
            if (c.ArgNames.Any(n => n != null)) diags.Error("TN2014", c.Span, $"builtin '{c.Name}' takes positional arguments");
            if (LibraryBuiltins.Contains(c.Name)) return InferLibrary(c, expected);
            foreach (var a in c.Args) C(a);
            return InferBuiltin(c);
        }

        List<(string Name, TType Type)> ps;
        IReadOnlyList<string> typeVars;
        IReadOnlyList<string> dimVars = [];
        TType ret;
        if (_fns.TryGetValue(c.Name, out var f))
        {
            c.Target = f;
            _callSink.Add(f);
            ps = f.Params.Select(p => (p.Name, p.Type)).ToList();
            typeVars = f.TypeParams;
            dimVars = f.DimParams;
            ret = f.Ret;
            if (f.Kind == FnKind.Lemma && !lemmaCall)
                diags.Error("TN2013", c.Span, $"'{f.Name}' is a lemma; call it as a statement: do {f.Name}(...)");
            CalleeRules(f, c);
        }
        else if (_cases.TryGetValue(c.Name, out var cs))
        {
            c.Case = cs;
            ps = cs.Fields.Select(x => (x.Name, x.Type)).ToList();
            typeVars = cs.Owner.TypeParams;
            ret = TType.Named(cs.Owner, cs.Owner.TypeParams.Select(TType.Param).ToList());
        }
        else if (_types.TryGetValue(c.Name, out var rec) && rec.Kind == TypeKind.Record)
        {
            c.Record = rec;
            ps = rec.Fields.Select(x => (x.Name, x.Type)).ToList();
            typeVars = rec.TypeParams;
            ret = TType.Named(rec, rec.TypeParams.Select(TType.Param).ToList());
        }
        else
        {
            diags.Error("TN2001", c.Span, _types.TryGetValue(c.Name, out var it) && it.Kind == TypeKind.Interface
                ? $"interface '{c.Name}' cannot be constructed; construct a class that implements it" : $"unknown function '{c.Name}'");
            foreach (var a in c.Args) C(a);
            return TType.Error;
        }

        if (c.ShapeArg != null) diags.Error("TN2013", c.Span, $"'{c.Name}' does not take a shape argument");
        if (c.Args.Count != ps.Count)
        {
            diags.Error("TN2007", c.Span, $"'{c.Name}' takes {ps.Count} argument(s) but was given {c.Args.Count}");
            foreach (var a in c.Args) C(a);
            return TType.Error;
        }
        CheckArgNames(c, ps);

        var ghostArgs = c.Target?.IsGhost ?? false;
        var saved = _inSpec;
        if (ghostArgs) _inSpec = true;
        var inst = new Inst([.. typeVars], [.. dimVars]);
        var deferred = new List<int>();
        for (var i = 0; i < c.Args.Count; i++)
        {
            var arg = c.Args[i];
            var pt = ps[i].Type;
            var generic = typeVars.Count > 0 && pt.Contains(t => t.Kind == TK.Param) || dimVars.Count > 0 && pt.HasParams;
            if (generic && arg is Hole or Var or ArrayLit { Elems.Count: 0 } && (arg is not Var v || IsCtorName(v.Name))) { deferred.Add(i); continue; }
            C(arg, generic ? null : pt);
            inst.Arg = i;
            if (!Unify(pt, arg.Type, inst) && !Coerce(arg, pt)) ArgMismatch(c, ps[i], arg, inst);
        }
        if (deferred.Count > 0 && expected != null && typeVars.Any(t => !inst.Types.ContainsKey(t))) Unify(ret, expected, inst);
        foreach (var i in deferred)
        {
            var pt = ps[i].Type.Subst(inst.Types, inst.Dims);
            C(c.Args[i], pt);
            inst.Arg = i;
            if (!Unify(ps[i].Type, c.Args[i].Type, inst) && !Coerce(c.Args[i], ps[i].Type)) ArgMismatch(c, ps[i], c.Args[i], inst);
        }
        _inSpec = saved;

        foreach (var (pd, ad, i) in inst.Pending)
        {
            if (ShapeEq(c, pd.Subst(inst.Dims), ad)) continue;
            ArgMismatch(c, ps[i], c.Args[i], inst);
        }
        if (expected != null && typeVars.Any(t => !inst.Types.ContainsKey(t))) Unify(ret, expected, inst);
        var missing = typeVars.Where(t => !inst.Types.ContainsKey(t)).ToList();
        if (missing.Count > 0)
        {
            diags.Error("TN2021", c.Span, $"cannot infer type parameter(s) {string.Join(", ", missing)} of '{c.Name}'",
                "Annotate the variable the result is assigned to.");
            return TType.Error;
        }
        c.TypeArgs = inst.Types;
        c.DimArgs = inst.Dims;
        return ret.Subst(inst.Types, inst.Dims);
    }

    private void CalleeRules(FnDecl f, Call c)
    {
        if (f.IsAsync && !c.Awaited)
            diags.Error("TN2029", c.Span, $"'{f.Name}' is async, so its result must be awaited",
                "Write 'let x = await ...' ('set', 'return' and 'do' work too). 'await' is the whole value of a statement, so it cannot appear inside another expression.");
        else if (!f.IsAsync && c.Awaited)
            diags.Error("TN2029", c.Span, $"'{f.Name}' is not async, so it cannot be awaited", "Remove 'await'.");
        if (f.IsGhost && !_inSpec)
            diags.Error("TN2008", c.Span, $"'{f.Name}' is a {(f.Kind == FnKind.Spec ? "spec function" : "lemma")} and can only be used in specifications and ghost code");
        var impurity = f.Effects.Count > 0 ? "has effects" : "can throw";
        if (!f.IsPure && _inLambda > 0)
            diags.Error("TN2023", c.Span, $"'{f.Name}' {impurity} and cannot be called inside a lambda", "Lambdas are pure; call it in a statement instead.");
        else if (!f.IsPure && _inSpec)
            diags.Error("TN2006", c.Span, $"'{f.Name}' {impurity} and cannot be used in a specification or ghost code");
        else
        {
            foreach (var eff in f.Effects.Where(x => !_cur.Effects.Contains(x)))
                diags.Error("TN2006", c.Span, $"'{f.Name}' has the {eff} effect, but '{_cur.Name}' does not declare it",
                    $"Declare the effect on the caller: fn {_cur.Name}(...) -> ... effects {string.Join(", ", _cur.Effects.Append(eff).Distinct())}");
            c.ThrowSites.Clear();
            foreach (var t in f.AllThrows.Where(t => t.Decl != null))
                c.ThrowSites.Add(Route(t.Decl!, t, c.Span, $"'{f.Name}' may throw '{t.Name}'"));
        }
    }

    /// <summary>'x.m(args)': the method is found from the type of the receiver, which is a class or an interface.</summary>
    private TType InferMethodCall(Call c)
    {
        var recv = c.Args[0];
        var rt = C(recv);
        void Rest() { foreach (var a in c.Args.Skip(1)) C(a); }
        if (rt.IsError) { Rest(); return TType.Error; }
        if (rt.Kind != TK.Named || !(rt.Decl!.IsClass || rt.Decl.Kind == TypeKind.Interface))
        {
            diags.Error("TN2002", recv.Span, $"'.{c.Name}(...)' needs a class or interface value but found {rt}",
                rt.Kind == TK.Named ? "Records and unions have no methods; call a module function: name(x, ...)." : "Call a builtin or module function: name(x, ...).");
            Rest();
            return TType.Error;
        }
        var owner = rt.Decl;
        var f = owner.Methods.FirstOrDefault(m => m.Member == c.Name);
        if (f == null)
        {
            diags.Error("TN2001", c.Span, $"'{owner.Name}' has no method '{c.Name}'",
                owner.Methods.Count > 0 ? $"Its methods are: {string.Join(", ", owner.Methods.Select(m => m.Member))}." : null);
            Rest();
            return TType.Error;
        }
        c.Target = f;
        _callSink.Add(f);
        CalleeRules(f, c);
        var ps = f.Params.Skip(1).Select(p => (p.Name, p.Type)).ToList();
        if (c.Args.Count - 1 != ps.Count)
        {
            diags.Error("TN2007", c.Span, $"'{f.Name}' takes {ps.Count} argument(s) but was given {c.Args.Count - 1}");
            Rest();
            return TType.Error;
        }
        CheckArgNames(c, ps, skip: 1);
        var saved = _inSpec;
        if (f.IsGhost) _inSpec = true;
        for (var i = 0; i < ps.Count; i++)
        {
            var arg = c.Args[i + 1];
            C(arg, ps[i].Type);
            if (!Unify(ps[i].Type, arg.Type, new Inst([], [])) && !Coerce(arg, ps[i].Type))
                ArgMismatch(c, ps[i], arg, new Inst([], []));
        }
        _inSpec = saved;
        return f.Ret;
    }

    /// <summary>The one implicit conversion: a class value where an interface it implements is expected.</summary>
    private static bool Coerce(Expr e, TType want)
    {
        if (!want.IsInterface || !e.Type.IsClass || !e.Type.Decl!.Interfaces.Contains(want.Decl!)) return false;
        e.Upcast = want.Decl;
        return true;
    }

    private bool IsCtorName(string name) => _cases.TryGetValue(name, out var c) && c.Fields.Count == 0 && Lookup(name) == null;

    private void ArgMismatch(Call c, (string Name, TType Type) p, Expr arg, Inst inst)
    {
        if (arg.Type.IsError) return;
        var shapes = p.Type.Kind == TK.Tensor && arg.Type.Kind == TK.Tensor;
        var solved = inst.Dims.Count == 0 ? "" : $" (with {string.Join(", ", inst.Dims.Select(kv => $"{kv.Key} = {kv.Value}"))})";
        diags.Error(shapes ? "TN2003" : "TN2002", arg.Span,
            $"{(shapes ? "shape" : "type")} mismatch in argument '{p.Name}' of '{c.Name}': expected {p.Type}{solved} but found {arg.Type}");
    }

    private void CheckArgNames(Call c, List<(string Name, TType Type)> ps, int skip = 0)
    {
        var names = c.ArgNames.Skip(skip).ToList();
        var shown = skip > 0 ? $"x.{c.Name}" : c.Name;
        var named = names.Count(n => n != null);
        if (named == 0)
        {
            for (var i = 0; i < ps.Count; i++)
                for (var j = i + 1; j < ps.Count; j++)
                    if (ps[i].Type.Base.Same(ps[j].Type.Base) && !ps[i].Type.IsError)
                    {
                        diags.Error("TN2014", c.Span,
                            $"arguments to '{shown}' must be named because parameters '{ps[i].Name}' and '{ps[j].Name}' both have type {ps[i].Type}",
                            $"Write {shown}({string.Join(", ", ps.Select(p => p.Name + ": ..."))}).");
                        return;
                    }
            return;
        }
        if (named != names.Count || !names.SequenceEqual(ps.Select(p => p.Name)))
            diags.Error("TN2014", c.Span, $"named arguments to '{shown}' must name every parameter, in order: {string.Join(", ", ps.Select(p => p.Name))}");
    }

    private int _inLambda;

    /// <summary>Strings, numbers, dates, collections, maps, sets and options. Arguments are typed here, in order.</summary>
    private TType InferLibrary(Call c, TType? expected)
    {
        var n = c.Args.Count;
        if (c.ShapeArg != null) diags.Error("TN2013", c.Span, $"'{c.Name}' does not take a shape argument");
        var checkedArgs = new HashSet<int>();
        bool Arity(int count)
        {
            if (n == count) return true;
            diags.Error("TN2007", c.Span, $"'{c.Name}' takes {count} argument(s) but was given {n}");
            for (var i = 0; i < n; i++) if (c.Args[i] is not Lambda) Arg(i);
            return false;
        }
        TType Arg(int i, TType? want = null)
        {
            if (!checkedArgs.Add(i)) return c.Args[i].Type;
            if (c.Args[i] is Lambda l)
            {
                diags.Error("TN2023", l.Span, $"argument {i + 1} of '{c.Name}' is not a lambda");
                return l.Type = TType.Error;
            }
            C(c.Args[i], want);
            if (want != null) Mismatch(c.Args[i], want);
            return c.Args[i].Type;
        }
        TType? Elem(int i)
        {
            var t = Arg(i);
            if (t.IsError) return null;
            if (t.Kind == TK.Array) return t.Elem;
            diags.Error("TN2002", c.Args[i].Span, $"'{c.Name}' needs an array here but found {t}");
            return null;
        }
        (TType K, TType V)? MapArg(int i)
        {
            var t = Arg(i);
            if (t.IsError) return null;
            if (t.Kind == TK.Map) return (t.Key, t.Value);
            diags.Error("TN2002", c.Args[i].Span, $"'{c.Name}' needs a map here but found {t}");
            return null;
        }
        TType? SetArg(int i)
        {
            var t = Arg(i);
            if (t.IsError) return null;
            if (t.Kind == TK.Set) return t.Elem;
            diags.Error("TN2002", c.Args[i].Span, $"'{c.Name}' needs a set here but found {t}");
            return null;
        }
        TType? OptionArg(int i)
        {
            var t = Arg(i);
            if (t.IsError) return null;
            if (t.Kind == TK.Named && t.Decl!.Name == "Option" && t.Decl.Prelude) return t.Args[0];
            diags.Error("TN2002", c.Args[i].Span, $"'{c.Name}' needs an Option here but found {t}");
            return null;
        }
        TType Lam(int i, params TType[] ps)
        {
            if (c.Args[i] is not Lambda l)
            {
                diags.Error("TN2023", c.Args[i].Span, $"argument {i + 1} of '{c.Name}' must be a lambda, such as x => x > 0");
                C(c.Args[i]);
                return TType.Error;
            }
            if (l.Params.Count != ps.Length)
            {
                diags.Error("TN2023", l.Span, $"the lambda passed to '{c.Name}' takes {ps.Length} parameter(s) but declares {l.Params.Count}");
                return l.Type = TType.Error;
            }
            _scopes.Add([]);
            for (var k = 0; k < ps.Length; k++)
            {
                var name = l.Params[k];
                if (Lookup(name) != null || _global.Contains(name) || CoreBuiltins.Contains(name) || l.Params.Take(k).Contains(name))
                    diags.Error("TN2004", l.Span, $"lambda parameter '{name}' shadows another name", "Pick a name not already in scope.");
                _scopes[^1][name] = new VarInfo(ps[k], false, false, VarKind.Local);
            }
            l.ParamTypes = [.. ps];
            _inLambda++;
            var body = C(l.Body);
            _inLambda--;
            _scopes.RemoveAt(_scopes.Count - 1);
            if (body.Kind == TK.Unit) diags.Error("TN2023", l.Body.Span, "a lambda must produce a value");
            return l.Type = body;
        }
        void LamBool(int i, TType elem)
        {
            var t = Lam(i, elem);
            if (!t.IsError && t.Kind != TK.Bool) diags.Error("TN2002", ((Lambda)c.Args[i]).Body.Span, $"'{c.Name}' needs a condition (Bool) but the lambda produces {t}");
        }
        TType Text(int count, TType result)
        {
            if (Arity(count)) for (var i = 0; i < count; i++) Arg(i, TType.String);
            return result;
        }
        TType Ints(TType result, params TType[] ps)
        {
            if (Arity(ps.Length)) for (var i = 0; i < ps.Length; i++) Arg(i, ps[i]);
            return result;
        }

        switch (c.Name)
        {
            case "str_len" or "str_index_of":
                return Text(c.Name == "str_len" ? 1 : 2, TType.Int);
            case "str_contains" or "str_starts_with" or "str_ends_with" or "str_eq_ignore_case":
                return Text(2, TType.Bool);
            case "str_is_blank":
                return Text(1, TType.Bool);
            case "str_trim" or "str_upper" or "str_lower":
                return Text(1, TType.String);
            case "str_sub":
                return Ints(TType.String, TType.String, TType.Int, TType.Int);
            case "str_split":
                return Text(2, TType.ArrayOf(TType.String));
            case "str_join":
                return Ints(TType.String, TType.ArrayOf(TType.String), TType.String);
            case "to_str":
            {
                if (!Arity(1)) return TType.String;
                var t = Arg(0);
                if (!t.IsError && t.Kind is not (TK.String or TK.Int or TK.Int32 or TK.Bool or TK.Decimal or TK.Date))
                    diags.Error("TN2002", c.Args[0].Span, $"'to_str' formats String, Int, Int32, Bool, Decimal and Date values, not {t}");
                return TType.String;
            }
            case "parse_int":
                return Text(1, OptionOf(TType.Int));
            case "parse_decimal":
                return Text(1, OptionOf(TType.Decimal));
            case "parse_date":
                return Text(2, OptionOf(TType.Date));
            case "parse_time":
                return Ints(OptionOf(TType.Int), TType.String, TType.ArrayOf(TType.String));
            case "to_decimal" or "to_int":
            {
                if (!Arity(1)) return c.Name == "to_int" ? TType.Int : TType.Decimal;
                var t = Arg(0);
                var ok = c.Name == "to_int" ? t.Kind is TK.Int32 or TK.Decimal : t.Kind is TK.Int or TK.Int32;
                if (!t.IsError && !ok)
                    diags.Error("TN2002", c.Args[0].Span, $"'{c.Name}' converts {(c.Name == "to_int" ? "an Int32 or a Decimal" : "an Int or an Int32")}, not {t}");
                return c.Name == "to_int" ? TType.Int : TType.Decimal;
            }
            case "to_int32":
                return Ints(TType.Int32, TType.Int);
            case "dec_round":
                return Ints(TType.Decimal, TType.Decimal, TType.Int);
            case "has_bit":
                return Ints(TType.Bool, TType.Int, TType.Int);
            case "date":
                return Ints(TType.Date, TType.Int, TType.Int, TType.Int);
            case "is_valid_date":
                return Ints(TType.Bool, TType.Int, TType.Int, TType.Int);
            case "add_days":
                return Ints(TType.Date, TType.Date, TType.Int);
            case "days_between":
                return Ints(TType.Int, TType.Date, TType.Date);
            case "day_of_week" or "year" or "month" or "day":
                return Ints(TType.Int, TType.Date);
            case "append":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                if (e == null) { Arg(1); return TType.Error; }
                Arg(1, e);
                return TType.ArrayOf(e);
            }
            case "concat":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                if (e == null) { Arg(1); return TType.Error; }
                Arg(1, TType.ArrayOf(e));
                return TType.ArrayOf(e);
            }
            case "map":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                var u = e == null ? Lam(1, TType.Error) : Lam(1, e);
                return u.IsError || e == null ? TType.Error : TType.ArrayOf(u.Base);
            }
            case "filter" or "any" or "all" or "count" or "find" or "find_last":
            {
                var result = c.Name switch { "any" or "all" => TType.Bool, "count" => TType.Int, _ => TType.Error };
                if (!Arity(2)) return result;
                var e = Elem(0);
                LamBool(1, e ?? TType.Error);
                if (e == null) return result;
                return c.Name switch { "filter" => TType.ArrayOf(e), "find" or "find_last" => OptionOf(e), _ => result };
            }
            case "sum_by":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                var t = Lam(1, e ?? TType.Error);
                if (t.IsError) return TType.Error;
                if (t.Kind is not (TK.Int or TK.Int32 or TK.Decimal))
                {
                    diags.Error("TN2002", ((Lambda)c.Args[1]).Body.Span, $"'sum_by' adds Int, Int32 or Decimal values, not {t}");
                    return TType.Error;
                }
                return t.Base;
            }
            case "min_by" or "max_by" or "sort_by" or "sort_by_desc":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                var k = Lam(1, e ?? TType.Error);
                if (!k.IsError && !k.IsOrdered && k.Kind != TK.String || k.Kind == TK.Float)
                    diags.Error("TN2002", ((Lambda)c.Args[1]).Body.Span, $"'{c.Name}' needs a key that is Int, Int32, Decimal, Date or String, not {k}");
                if (e == null) return TType.Error;
                return c.Name is "min_by" or "max_by" ? OptionOf(e) : TType.ArrayOf(e);
            }
            case "group_by":
            {
                if (!Arity(2)) return TType.Error;
                var e = Elem(0);
                var k = Lam(1, e ?? TType.Error);
                if (!k.IsError) CheckKey(k, ((Lambda)c.Args[1]).Body.Span);
                return e == null || k.IsError ? TType.Error : TType.MapOf(k.Base, TType.ArrayOf(e));
            }
            case "to_map":
            {
                if (!Arity(3)) return TType.Error;
                var e = Elem(0);
                var k = Lam(1, e ?? TType.Error);
                var v = Lam(2, e ?? TType.Error);
                if (!k.IsError) CheckKey(k, ((Lambda)c.Args[1]).Body.Span);
                return e == null || k.IsError || v.IsError ? TType.Error : TType.MapOf(k.Base, v.Base);
            }
            case "fold":
            {
                if (!Arity(3)) return TType.Error;
                var e = Elem(0);
                checkedArgs.Add(1);
                var acc = C(c.Args[1], expected);
                var t = Lam(2, acc.Base, e ?? TType.Error);
                if (!t.IsError && !acc.IsError) Mismatch(((Lambda)c.Args[2]).Body, acc.Base);
                return acc.Base;
            }
            case "map_empty" or "set_empty":
            {
                var kind = c.Name == "map_empty" ? TK.Map : TK.Set;
                if (!Arity(0)) return TType.Error;
                if (expected?.Kind == kind) return expected.Base;
                diags.Error("TN2021", c.Span, $"cannot infer the type of '{c.Name}()'",
                    $"Annotate it: let m: {(kind == TK.Map ? "Map[String, Int]" : "Set[Int]")} = {c.Name}()");
                return TType.Error;
            }
            case "map_put":
            {
                if (!Arity(3)) return TType.Error;
                if (MapArg(0) is not { } kv) { Arg(1); Arg(2); return TType.Error; }
                Arg(1, kv.K); Arg(2, kv.V);
                return TType.MapOf(kv.K, kv.V);
            }
            case "map_get" or "map_has" or "map_remove":
            {
                if (!Arity(2)) return TType.Error;
                if (MapArg(0) is not { } kv) { Arg(1); return c.Name == "map_has" ? TType.Bool : TType.Error; }
                Arg(1, kv.K);
                return c.Name switch { "map_get" => OptionOf(kv.V), "map_has" => TType.Bool, _ => TType.MapOf(kv.K, kv.V) };
            }
            case "map_get_or":
            {
                if (!Arity(3)) return TType.Error;
                if (MapArg(0) is not { } kv) { Arg(1); Arg(2); return TType.Error; }
                Arg(1, kv.K); Arg(2, kv.V);
                return kv.V;
            }
            case "map_size" or "map_keys" or "map_values":
            {
                if (!Arity(1)) return c.Name == "map_size" ? TType.Int : TType.Error;
                if (MapArg(0) is not { } kv) return c.Name == "map_size" ? TType.Int : TType.Error;
                return c.Name switch { "map_size" => TType.Int, "map_keys" => TType.ArrayOf(kv.K), _ => TType.ArrayOf(kv.V) };
            }
            case "set_of":
            {
                if (!Arity(1)) return TType.Error;
                var e = Elem(0);
                if (e == null) return TType.Error;
                CheckKey(e, c.Args[0].Span);
                return TType.SetOf(e);
            }
            case "set_add" or "set_has":
            {
                if (!Arity(2)) return c.Name == "set_has" ? TType.Bool : TType.Error;
                var e = SetArg(0);
                if (e == null) { Arg(1); return c.Name == "set_has" ? TType.Bool : TType.Error; }
                Arg(1, e);
                return c.Name == "set_has" ? TType.Bool : TType.SetOf(e);
            }
            case "set_size" or "set_items":
            {
                if (!Arity(1)) return c.Name == "set_size" ? TType.Int : TType.Error;
                var e = SetArg(0);
                if (e == null) return c.Name == "set_size" ? TType.Int : TType.Error;
                return c.Name == "set_size" ? TType.Int : TType.ArrayOf(e);
            }
            case "is_some" or "is_none":
                if (Arity(1)) OptionArg(0);
                return TType.Bool;
            case "unwrap_or":
            {
                if (!Arity(2)) return TType.Error;
                var t = OptionArg(0);
                if (t == null) { Arg(1); return TType.Error; }
                Arg(1, t);
                return t;
            }
            default:
                throw new InvalidOperationException(c.Name);
        }
    }

    private TType InferBuiltin(Call c)
    {
        TType Arg(int i) => c.Args[i].Type;
        bool Arity(int n)
        {
            if (c.Args.Count == n) return true;
            diags.Error("TN2007", c.Span, $"'{c.Name}' takes {n} argument(s) but was given {c.Args.Count}");
            return false;
        }
        bool Want(int i, TType t)
        {
            if (Arg(i).IsError) return false;
            Mismatch(c.Args[i], t);
            return Arg(i).Same(t);
        }
        bool Rank(int i, int rank)
        {
            if (Arg(i).IsError) return false;
            if (Arg(i).Kind == TK.Tensor && (rank < 0 || Arg(i).Dims.Count == rank)) return true;
            diags.Error("TN2003", c.Args[i].Span, $"'{c.Name}' expects {(rank < 0 ? "a tensor" : $"a rank-{rank} tensor")} here but found {Arg(i)}");
            return false;
        }
        TType ShapeError(string detail)
        {
            diags.Error("TN2003", c.Span, $"shape mismatch in '{c.Name}': {detail}");
            return TType.Error;
        }
        bool SameShape(TType a, TType b)
        {
            if (a.ElemType != b.ElemType || a.Dims.Count != b.Dims.Count) return false;
            for (var k = 0; k < a.Dims.Count; k++) if (!ShapeEq(c, a.Dims[k], b.Dims[k])) return false;
            return true;
        }
        TType? Shape()
        {
            if (c.ShapeArg == null) { diags.Error("TN2013", c.Span, $"'{c.Name}' needs a shape: {c.Name}[d1, d2, ...](...)"); return null; }
            var s = Resolve(c.ShapeArg, TypeSet, DimSet, c.Span);
            c.ShapeArg = s;
            return s;
        }
        if (c.ShapeArg != null && c.Name is not ("reshape" or "full")) diags.Error("TN2013", c.Span, $"'{c.Name}' does not take a shape argument");
        if (c.Name == "row_sum" && !_inSpec) diags.Error("TN2008", c.Span, "'row_sum' is specification-only (it is evaluated in the real-number tensor model)");

        switch (c.Name)
        {
            case "len":
                if (!Arity(1) || Arg(0).IsError) return TType.Int;
                if (Arg(0).Kind != TK.Array) diags.Error("TN2002", c.Args[0].Span, $"'len' needs an array but found {Arg(0)}");
                return TType.Int;
            case "update":
                if (!Arity(3) || Arg(0).IsError) return TType.Error;
                if (Arg(0).Kind != TK.Array) { diags.Error("TN2002", c.Args[0].Span, $"'update' needs an array but found {Arg(0)}"); return TType.Error; }
                Want(1, TType.Int); Want(2, Arg(0).Elem!);
                return Arg(0).Base;
            case "fill":
                if (!Arity(2)) return TType.Error;
                Want(0, TType.Int);
                if (Arg(1).Kind == TK.Unit) diags.Error("TN2002", c.Args[1].Span, "Array[Unit] is not a valid type");
                return Arg(1).IsError ? TType.Error : TType.ArrayOf(Arg(1).Base);
            case "to_float":
                if (Arity(1)) Want(0, TType.Int);
                return TType.Float;
            case "trunc":
                if (Arity(1)) Want(0, TType.Float);
                return TType.Int;
            case "matmul":
                if (!Arity(2) || !(Rank(0, 2) & Rank(1, 2))) return TType.Error;
                if (Arg(0).ElemType != Arg(1).ElemType) return ShapeError($"element types differ ({Arg(0)} and {Arg(1)})");
                return ShapeEq(c, Arg(0).Dims[1], Arg(1).Dims[0])
                    ? TType.Tensor(Arg(0).ElemType, [Arg(0).Dims[0], Arg(1).Dims[1]])
                    : ShapeError($"inner dimensions differ ({Arg(0).Dims[1]} vs {Arg(1).Dims[0]}) for {Arg(0)} and {Arg(1)}");
            case "add" or "sub" or "mul" or "relu_grad" or "tanh_grad" or "sigmoid_grad" or "softmax_grad":
                if (!Arity(2) || !(Rank(0, c.Name == "softmax_grad" ? 2 : -1) & Rank(1, -1))) return TType.Error;
                return SameShape(Arg(0), Arg(1))
                    ? Arg(0).Base
                    : ShapeError($"{Arg(0)} and {Arg(1)} differ; there is no implicit broadcasting{(c.Name == "add" ? " (use add_bias for a bias vector)" : "")}");
            case "scale":
                if (!Arity(2) || !Rank(0, -1)) return TType.Error;
                Want(1, TType.Float);
                return Arg(0).Base;
            case "add_bias":
                if (!Arity(2) || !(Rank(0, 2) & Rank(1, 1))) return TType.Error;
                return Arg(0).ElemType == Arg(1).ElemType && ShapeEq(c, Arg(0).Dims[1], Arg(1).Dims[0])
                    ? Arg(0).Base
                    : ShapeError($"bias {Arg(1)} does not match the last dimension of {Arg(0)}");
            case "relu" or "tanh" or "sigmoid":
                return Arity(1) && Rank(0, -1) ? Arg(0).Base : TType.Error;
            case "softmax":
                return Arity(1) && Rank(0, 2) ? Arg(0).Base : TType.Error;
            case "transpose":
                return Arity(1) && Rank(0, 2) ? TType.Tensor(Arg(0).ElemType, [Arg(0).Dims[1], Arg(0).Dims[0]]) : TType.Error;
            case "sum_rows":
                return Arity(1) && Rank(0, 2) ? TType.Tensor(Arg(0).ElemType, [Arg(0).Dims[1]]) : TType.Error;
            case "reshape":
            {
                var s = Shape();
                if (s == null || !Arity(1) || !Rank(0, -1)) return TType.Error;
                var target = TType.Tensor(Arg(0).ElemType, s.Dims);
                return ShapeEq(c, Dim.Product(Arg(0).Dims), Dim.Product(s.Dims))
                    ? target
                    : ShapeError($"{Arg(0)} has a different number of elements than {target}");
            }
            case "full":
            {
                var s = Shape();
                if (Arity(1)) Want(0, TType.Float);
                return s ?? TType.Error;
            }
            case "sum":
                return Arity(1) && Rank(0, -1) ? TType.Float : TType.Error;
            case "to_f32" or "to_f64":
                return Arity(1) && Rank(0, -1) ? TType.Tensor(c.Name == "to_f32" ? ElemType.Float32 : ElemType.Float64, Arg(0).Dims) : TType.Error;
            case "row_sum":
                if (!Arity(2) || !Rank(0, 2)) return TType.Float;
                Want(1, TType.Int);
                return TType.Float;
            default:
                throw new InvalidOperationException(c.Name);
        }
    }
}
