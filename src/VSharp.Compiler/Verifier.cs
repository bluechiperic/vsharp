using System.Numerics;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Z3;

namespace VSharp.Compiler;

/// <summary>
/// Proves every obligation of a checked module: contracts, loop invariants, termination, refinements, tensor shapes, and
/// the absence of division by zero, out-of-bounds indexing and (in total mode) integer overflow. Each function is executed
/// symbolically; branches are merged at join points. Each obligation becomes one SMT query that asks Z3 for a state that
/// violates it.
/// </summary>
public sealed class Verifier(ModuleDecl module, DiagnosticBag diags, IReadOnlyList<string> sources, int timeoutMs = 5000, Action<string, string>? smtSink = null)
{
    public Verifier(ModuleDecl module, DiagnosticBag diags, string source, int timeoutMs = 5000, Action<string, string>? smtSink = null)
        : this(module, diags, [source], timeoutMs, smtSink) { }

    /// <summary>
    /// Strings, decimals and dates. A Date is its DayNumber (days since 0001-01-01); the calendar functions are Howard
    /// Hinnant's exact civil-from-days and days-from-civil algorithms, so year/month/day are computed, not assumed.
    /// </summary>
    private const string LibraryPrelude = """
        (define-fun s.int ((x Int)) String (ite (>= x 0) (str.from_int x) (str.++ "-" (str.from_int (- x)))))
        (declare-fun s.dec (Real) String)
        (declare-fun s.date (Int) String)
        (declare-fun s.trim (String) String)
        (declare-fun s.upper (String) String)
        (declare-fun s.lower (String) String)
        (declare-fun d.round (Real Int) Real)
        (define-fun d.era ((n Int)) Int (div (+ n 306) 146097))
        (define-fun d.doe ((n Int)) Int (- (+ n 306) (* 146097 (d.era n))))
        (define-fun d.yoe ((n Int)) Int
          (div (- (+ (- (d.doe n) (div (d.doe n) 1460)) (div (d.doe n) 36524)) (div (d.doe n) 146096)) 365))
        (define-fun d.doy ((n Int)) Int (- (d.doe n) (- (+ (* 365 (d.yoe n)) (div (d.yoe n) 4)) (div (d.yoe n) 100))))
        (define-fun d.mp ((n Int)) Int (div (+ (* 5 (d.doy n)) 2) 153))
        (define-fun d.day ((n Int)) Int (+ (- (d.doy n) (div (+ (* 153 (d.mp n)) 2) 5)) 1))
        (define-fun d.month ((n Int)) Int (ite (< (d.mp n) 10) (+ (d.mp n) 3) (- (d.mp n) 9)))
        (define-fun d.year ((n Int)) Int (+ (d.yoe n) (* 400 (d.era n)) (ite (<= (d.month n) 2) 1 0)))
        (define-fun d.from ((y Int) (m Int) (d Int)) Int
          (let ((yy (- y (ite (<= m 2) 1 0))))
          (let ((era (div yy 400)))
          (let ((yoe (- yy (* 400 era))))
          (let ((doy (+ (div (+ (* 153 (ite (> m 2) (- m 3) (+ m 9))) 2) 5) (- d 1))))
            (- (+ (* 146097 era) (* 365 yoe) (div yoe 4) (- (div yoe 100)) doy) 306))))))
        (define-fun d.leap ((y Int)) Bool (and (= (mod y 4) 0) (or (not (= (mod y 100) 0)) (= (mod y 400) 0))))
        (define-fun d.dim ((y Int) (m Int)) Int
          (ite (= m 2) (ite (d.leap y) 29 28) (ite (or (= m 4) (= m 6) (= m 9) (= m 11)) 30 31)))
        (define-fun d.valid ((y Int) (m Int) (d Int)) Bool (and (<= 1 y 9999) (<= 1 m 12) (<= 1 d (d.dim y m))))

        """;

    /// <summary>Declarations that use the datatypes (arrays and the prelude Option type).</summary>
    private const string TypedPrelude = """
        (declare-fun s.split (String String) (Arr String))
        (declare-fun s.join ((Arr String) String) String)
        (declare-fun s.parse_int (String) (t.Option Int))
        (declare-fun s.parse_dec (String) (t.Option Real))
        (declare-fun s.parse_date (String String) (t.Option Int))
        (declare-fun s.parse_time (String (Arr String)) (t.Option Int))

        """;

    private const int MaxDay = 3652058;
    private const string MinInt32 = "(- 2147483648)";
    private const string MaxInt32 = "2147483647";
    private const string Prelude = """
        (define-sort F64 () (_ FloatingPoint 11 53))
        (declare-sort Tensor 0)
        ; V# division truncates toward zero (as IL 'div' does); SMT-LIB 'div' is Euclidean.
        (define-fun tdiv ((a Int) (b Int)) Int
          (ite (>= a 0) (ite (> b 0) (div a b) (- (div a (- b))))
                        (ite (> b 0) (- (div (- a) b)) (div (- a) (- b)))))
        (define-fun tmod ((a Int) (b Int)) Int (- a (* b (tdiv a b))))
        ; Real-number tensor model: element i (row-major) of a tensor, and the sum of row k of a matrix.
        (declare-fun el (Tensor Int) Real)
        (declare-fun row_sum (Tensor Int) Real)
        (declare-fun tf.sum (Tensor) F64)
        (declare-fun tf.matmul (Tensor Tensor) Tensor)
        (declare-fun tf.add (Tensor Tensor) Tensor)
        (declare-fun tf.sub (Tensor Tensor) Tensor)
        (declare-fun tf.mul (Tensor Tensor) Tensor)
        (declare-fun tf.scale (Tensor F64) Tensor)
        (declare-fun tf.add_bias (Tensor Tensor) Tensor)
        (declare-fun tf.relu (Tensor) Tensor)
        (declare-fun tf.tanh (Tensor) Tensor)
        (declare-fun tf.sigmoid (Tensor) Tensor)
        (declare-fun tf.softmax (Tensor) Tensor)
        (declare-fun tf.transpose (Tensor) Tensor)
        (declare-fun tf.sum_rows (Tensor) Tensor)
        (declare-fun tf.to_f32 (Tensor) Tensor)
        (declare-fun tf.to_f64 (Tensor) Tensor)
        (declare-fun tf.relu_grad (Tensor Tensor) Tensor)
        (declare-fun tf.tanh_grad (Tensor Tensor) Tensor)
        (declare-fun tf.sigmoid_grad (Tensor Tensor) Tensor)
        (declare-fun tf.softmax_grad (Tensor Tensor) Tensor)

        """;

    private const string MinInt = "(- 9223372036854775808)";
    private const string MaxInt = "9223372036854775807";
    private const int ArrayPreview = 6;

    private sealed class State
    {
        public Dictionary<string, (string Term, TType Type)> Store = [];
        public List<string> Path = [];
        /// <summary>Source-level facts, reported at typed holes.</summary>
        public List<string> Facts = [];
        public State Clone() => new() { Store = new(Store), Path = [.. Path], Facts = [.. Facts] };
    }

    /// <summary>One translation of an expression to an SMT term.</summary>
    private sealed class Tx(State s, Dictionary<string, (string Term, TType Type)> env)
    {
        /// <summary>Proof context for obligations, and where instantiated facts are recorded.</summary>
        public State S { get; } = s;
        public Dictionary<string, (string Term, TType Type)> Env { get; } = env;
        /// <summary>Emit well-definedness obligations (bounds, division, preconditions, termination, shapes).</summary>
        public bool Checks { get; init; }
        /// <summary>Assume the contract of every function applied in the expression.</summary>
        public bool Instantiate { get; init; }
        /// <summary>The expression runs (it is not specification or ghost code), so total mode checks overflow.</summary>
        public bool Exec { get; init; }
        /// <summary>Type arguments when translating a callee's contract.</summary>
        public Dictionary<string, TType> Types { get; init; } = [];
        /// <summary>Enclosing guards and quantifier binders, outermost first. Binder text is "(sym Sort)".</summary>
        public List<(bool Binder, string Text)> Ctx { get; } = [];
        public Dictionary<string, string> Bound { get; } = [];
    }

    private sealed class HoleInfo
    {
        public required Hole Hole { get; init; }
        public required string Sym { get; init; }
        public required List<string> Facts { get; init; }
        public required Dictionary<string, string> Scope { get; init; }
        public List<string> Obligations { get; } = [];
    }

    private enum Verdict { Proved, Refuted, Unknown }

    private readonly Context _z3 = new(new Dictionary<string, string> { ["model"] = "true" });
    private string _typeDecls = "";
    private string _fnDecls = "";
    private FnDecl _cur = null!;
    private List<string> _decls = [];
    private HashSet<string> _declared = [];
    private List<string>? _measure;
    private readonly List<HoleInfo> _holes = [];
    private int _fresh;
    private int _queries;

    public int Queries => _queries;

    public void Verify()
    {
        _typeDecls = Datatypes();
        var sb = new StringBuilder();
        foreach (var f in module.Fns.Where(HasSymbol).Where(f => !f.IsGeneric))
            sb.AppendLine($"(declare-fun f.{f.Name} ({string.Join(" ", f.DimParams.Select(_ => "Int").Concat(f.Params.Select(p => SortOf(p.Type, f))))}) {SortOf(f.Ret, f)})");
        foreach (var t in module.Types.Where(t => t.IsClass))
            foreach (var i in t.Interfaces)
                sb.AppendLine($"(declare-fun {Up(t, i)} (t.{t.Name}) t.{i.Name})");
        // Dispatch: an interface method applied to an upcast class value is that class's method.
        foreach (var cm in module.Fns.Where(f => f.Implements != null && HasSymbol(f.Implements)))
        {
            var im = cm.Implements!;
            var binders = cm.Params.Select((p, k) => (Sym: $"a!{k}", Sort: SortOf(p.Type, cm))).ToList();
            var rest = string.Concat(binders.Skip(1).Select(b => " " + b.Sym));
            var viaInterface = $"(f.{im.Name} ({Up(cm.Owner!, im.Owner!)} a!0){rest})";
            sb.AppendLine($"(assert (forall ({string.Join(" ", binders.Select(b => $"({b.Sym} {b.Sort})"))}) " +
                          $"(! (= {viaInterface} (f.{cm.Name} a!0{rest})) :pattern ({viaInterface}))))");
        }
        _fnDecls = sb.ToString();
        foreach (var t in module.Types.Where(t => t.Kind == TypeKind.Refinement && !t.Prelude)) VerifyType(t);
        foreach (var t in module.Types.Where(t => t.Invariants.Count > 0)) VerifyInvariants(t);
        foreach (var c in module.Consts) VerifyConst(c);
        foreach (var f in module.Fns) VerifyFn(f);
    }

    /// <summary>A constant's value must be well defined (valid dates, in-bounds substrings, ...) and satisfy its type.</summary>
    private void VerifyConst(ConstDecl c)
    {
        Begin(new FnDecl { Name = c.Name, NameSpan = c.NameSpan });
        var s = new State();
        var v = T(c.Value, CodeTx(s, false));
        if (c.Type.Refine != null) ProveRefine(s, c.Type, v, c.Value.Span, $"constant '{c.Name}'");
    }

    private static bool HasSymbol(FnDecl f) => f.IsPure && f.Ret.Kind != TK.Unit && f.Kind != FnKind.Lemma;

    /// <summary>The function that views a class value as one of its interfaces.</summary>
    private static string Up(TypeDecl cls, TypeDecl iface) => $"up.{cls.Name}.{iface.Name}";

    /// <summary>
    /// The environment for reading an interface method's contract on behalf of an implementation: the same
    /// parameters, with 'self' viewed as the interface.
    /// </summary>
    private static Dictionary<string, (string Term, TType Type)> Inherited(FnDecl impl, Dictionary<string, (string Term, TType Type)> env)
    {
        var im = impl.Implements!;
        return new Dictionary<string, (string Term, TType Type)>(env)
        {
            ["self"] = ($"({Up(impl.Owner!, im.Owner!)} {env["self"].Term})", im.Params[0].Type),
        };
    }

    /// <summary>A class invariant must be well defined; each clause may rely on the ones before it.</summary>
    private void VerifyInvariants(TypeDecl t)
    {
        Begin(new FnDecl { Name = t.Name, NameSpan = t.NameSpan });
        var s = new State();
        var self = TType.Named(t, []);
        var sym = Fresh(self, "self");
        Bind(s, "self", sym, self);
        foreach (var inv in t.Invariants) s.Path.Add(T(inv, SpecTx(s)));
    }

    /// <summary>The invariant of class <paramref name="t"/> for the value <paramref name="term"/>.</summary>
    private List<string> Invariant(TypeDecl t, string term, State sink, bool instantiate) =>
        t.Invariants.Select(inv => T(inv, new Tx(sink, new Dictionary<string, (string, TType)> { ["self"] = (term, TType.Named(t, [])) }) { Instantiate = instantiate })).ToList();

    /// <summary>Nesting depth of facts that are stated for every element of a collection (inside a 'forall').</summary>
    private int _perElement;

    /// <summary>
    /// The invariant as an assumption, with the contracts of the functions it applies (a spec function's definition,
    /// say), which hold everywhere. Under a quantifier a fresh constant would be shared by every element, so there the
    /// facts are dropped when the translation created one.
    /// </summary>
    private List<string> AssumedInvariant(TypeDecl t, string term)
    {
        var sink = new State();
        var before = _decls.Count;
        var facts = Invariant(t, term, sink, instantiate: true);
        if (_perElement > 0 && _decls.Skip(before).Any(d => d.Contains('!'))) return facts;
        return [.. facts, .. sink.Path];
    }

    /// <summary>Every construction of a class value, by a constructor call or 'with', must establish its invariant.</summary>
    private void ProveInvariant(Tx tx, TypeDecl t, string term, Span span)
    {
        if (!tx.Checks || t.Invariants.Count == 0) return;
        var facts = Invariant(t, term, tx.S, instantiate: true);
        for (var k = 0; k < facts.Count; k++)
            Oblige(tx, facts[k], "TN3016", $"invariant of class '{t.Name}' might not hold: {Text(t.Invariants[k])}", span,
                $"Every '{t.Name}' value must satisfy its invariants when it is built. Check the arguments first, or add a precondition.");
    }

    // ---------- sorts ----------

    /// <summary>
    /// One declare-datatypes block per group of mutually recursive types, dependencies first. Z3 crashes when a block
    /// declares a generic datatype together with another datatype that instantiates it (a record with an Option field).
    /// </summary>
    private string Datatypes()
    {
        // Maps and sets keep a lookup array, their size, and their keys (items) in insertion order.
        var decls = new Dictionary<string, (string Head, string Body, HashSet<string> Deps)>
        {
            ["Arr"] = ("(Arr 1)", "(par (p!T) ((mk (elems (Array Int p!T)) (alen Int))))", []),
            ["Mp"] = ("(Mp 2)", "(par (p!K p!V) ((mkm (mget (Array p!K (t.Option p!V))) (msize Int) (mkeys (Arr p!K)))))", ["Option", "Arr"]),
            ["St"] = ("(St 1)", "(par (p!T) ((mks (smem (Array p!T Bool)) (ssize Int) (sitems (Arr p!T)))))", ["Arr"]),
        };
        static void DepsOf(TType t, HashSet<string> into)
        {
            switch (t.Kind)
            {
                case TK.Array: into.Add("Arr"); DepsOf(t.Elem!, into); break;
                case TK.Set: into.Add("St"); into.Add("Arr"); DepsOf(t.Elem!, into); break;
                case TK.Map: into.Add("Mp"); into.Add("Option"); into.Add("Arr"); DepsOf(t.Key, into); DepsOf(t.Value, into); break;
                case TK.Named:
                    into.Add(t.Name!);
                    foreach (var a in t.Args) DepsOf(a, into);
                    break;
            }
        }
        foreach (var t in module.Types.Where(t => t.Kind is TypeKind.Record or TypeKind.Union))
        {
            string Field(FieldDecl f, string owner) => $"(s.{owner}.{f.Name} {SortIn(f.Type, p => $"p!{p}")})";
            var ctors = t.Kind == TypeKind.Record
                ? [$"(c.{t.Name} {string.Join(" ", t.Fields.Select(f => Field(f, t.Name)))})"]
                : t.Cases.Select(c => c.Fields.Count == 0 ? $"(c.{c.Name})" : $"(c.{c.Name} {string.Join(" ", c.Fields.Select(f => Field(f, c.Name)))})").ToList();
            var body = $"({string.Join(" ", ctors)})";
            var deps = new HashSet<string>();
            foreach (var f in t.Kind == TypeKind.Record ? t.Fields : t.Cases.SelectMany(c => c.Fields)) DepsOf(f.Type, deps);
            decls[t.Name] = ($"(t.{t.Name} {t.TypeParams.Count})",
                t.TypeParams.Count == 0 ? body : $"(par ({string.Join(" ", t.TypeParams.Select(p => $"p!{p}"))}) {body})", deps);
        }

        // Tarjan's algorithm yields strongly connected components with every dependency before its dependents.
        var index = new Dictionary<string, int>();
        var low = new Dictionary<string, int>();
        var stack = new Stack<string>();
        var groups = new List<List<string>>();
        void Visit(string n)
        {
            index[n] = low[n] = index.Count;
            stack.Push(n);
            foreach (var d in decls[n].Deps.Where(decls.ContainsKey))
            {
                if (!index.ContainsKey(d)) { Visit(d); low[n] = Math.Min(low[n], low[d]); }
                else if (stack.Contains(d)) low[n] = Math.Min(low[n], index[d]);
            }
            if (low[n] != index[n]) return;
            var group = new List<string>();
            string m;
            do { m = stack.Pop(); group.Add(m); } while (m != n);
            groups.Add(group);
        }
        foreach (var n in decls.Keys.ToList()) if (!index.ContainsKey(n)) Visit(n);

        // An interface value is opaque: what is known about it comes from its methods' contracts.
        var sb = new System.Text.StringBuilder();
        foreach (var t in module.Types.Where(t => t.Kind == TypeKind.Interface)) sb.Append($"(declare-sort t.{t.Name} 0)\n");
        foreach (var g in groups)
            sb.Append($"(declare-datatypes ({string.Join(" ", g.Select(n => decls[n].Head))})\n  ({string.Join("\n   ", g.Select(n => decls[n].Body))}))\n");
        return sb.ToString();
    }

    private static string SortIn(TType t, Func<string, string> param) => t.Kind switch
    {
        TK.Int or TK.Int32 or TK.Date => "Int",
        TK.Float => "F64",
        TK.String => "String",
        TK.Decimal => "Real",
        TK.Array => $"(Arr {SortIn(t.Elem!, param)})",
        TK.Map => $"(Mp {SortIn(t.Key, param)} {SortIn(t.Value, param)})",
        TK.Set => $"(St {SortIn(t.Elem!, param)})",
        TK.Tensor => "Tensor",
        TK.Named => t.Args.Count == 0 ? $"t.{t.Name}" : $"(t.{t.Name} {string.Join(" ", t.Args.Select(a => SortIn(a, param)))})",
        TK.Param => param(t.Name!),
        _ => "Bool",
    };

    private static string SortOf(TType t, FnDecl owner) => SortIn(t, p => $"p.{owner.Name}.{p}");

    private string Sort(TType t, Tx? tx = null) => SortOf(tx == null || tx.Types.Count == 0 ? t : t.Subst(tx.Types, new Dictionary<string, Dim>()), _cur);

    private static string Mangle(TType t, FnDecl owner) => t.Kind switch
    {
        TK.Array => $"Arr<{Mangle(t.Elem!, owner)}>",
        TK.Set => $"Set<{Mangle(t.Elem!, owner)}>",
        TK.Map => $"Map<{Mangle(t.Key, owner)},{Mangle(t.Value, owner)}>",
        TK.Named => t.Args.Count == 0 ? t.Name! : $"{t.Name}<{string.Join(",", t.Args.Select(a => Mangle(a, owner)))}>",
        TK.Param => $"{owner.Name}.{t.Name}",
        _ => SortIn(t, p => p),
    };

    private void Declare(string decl)
    {
        if (_declared.Add(decl)) _decls.Add(decl);
    }

    private string FnSym(FnDecl f, Dictionary<string, TType> typeArgs)
    {
        if (!f.IsGeneric) return $"f.{f.Name}";
        var args = f.TypeParams.Select(p => typeArgs[p]).ToList();
        var sym = $"|f.{f.Name}<{string.Join(",", args.Select(a => Mangle(a, _cur)))}>|";
        var map = Checker.Map(f.TypeParams, args);
        var dims = new Dictionary<string, Dim>();
        Declare($"(declare-fun {sym} ({string.Join(" ", f.DimParams.Select(_ => "Int").Concat(f.Params.Select(p => Sort(p.Type.Subst(map, dims)))))}) {Sort(f.Ret.Subst(map, dims))})");
        return sym;
    }

    // ---------- functions ----------

    private Tx SpecTx(State s) => new(s, s.Store) { Checks = true, Instantiate = true };
    private Tx CodeTx(State s, bool ghost) => new(s, s.Store) { Checks = true, Instantiate = true, Exec = !ghost };

    private void Begin(FnDecl f)
    {
        _cur = f;
        _decls = [];
        _declared = [];
        _measure = null;
        foreach (var p in f.TypeParams) Declare($"(declare-sort p.{f.Name}.{p} 0)");
    }

    private void VerifyType(TypeDecl t)
    {
        var owner = new FnDecl { Name = t.Name, NameSpan = t.NameSpan };
        owner.TypeParams.AddRange(t.TypeParams);
        Begin(owner);
        var s = new State();
        Bind(s, "self", Fresh(t.Base!, "self"), t.Base!);
        T(t.Pred!, SpecTx(s));
    }

    private void VerifyFn(FnDecl f)
    {
        Begin(f);
        var s = new State();
        foreach (var d in f.DimParams)
        {
            var sym = $"d.{d}";
            Declare($"(declare-const {sym} Int)");
            Bind(s, d, sym, TType.Int);
            s.Path.Add($"(> {sym} 0)");
        }
        foreach (var p in f.Params)
        {
            var sym = $"v.{p.Name}";
            Declare($"(declare-const {sym} {Sort(p.Type)})");
            Bind(s, p.Name, sym, p.Type);
            Assume(s, p.Type, sym);
        }
        if (f.Implements is { } im)
            foreach (var r in im.Requires)
            {
                s.Path.Add(T(r, new Tx(s, Inherited(f, s.Store)) { Checks = true, Instantiate = true }));
                s.Facts.Add(Text(r));
            }
        foreach (var r in f.Requires)
        {
            s.Path.Add(T(r, SpecTx(s)));
            s.Facts.Add(Text(r));
        }
        foreach (var t in f.Throws.Where(t => t.When != null)) T(t.When!, SpecTx(s.Clone()));
        if (f.Requires.Count > 0 && Query(s, "false", "vacuity").Verdict == Verdict.Proved)
            diags.Warning("TN3009", f.NameSpan, $"the preconditions of '{f.Name}' can never hold, so it verifies vacuously",
                "No caller can satisfy the 'requires' clauses. Check them for a contradiction.");
        if (f.Decreases.Count > 0) _measure = f.Decreases.Select(d => T(d, SpecTx(s))).ToList();

        // The contract must itself be well defined: check each 'ensures' against an arbitrary result.
        var w = s.Clone();
        var anyResult = f.Ret.Kind == TK.Unit ? "true" : Fresh(f.Ret, "result");
        Bind(w, "result", anyResult, f.Ret);
        Assume(w, f.Ret, anyResult);
        foreach (var e in f.Ensures) w.Path.Add(T(e, SpecTx(w)));

        switch (f.Kind)
        {
            case FnKind.Fn when f.IsAbstract:
                break;
            case FnKind.Fn or FnKind.Grad or FnKind.Lemma:
                var end = Exec(f.Body, s);
                if (end != null && f.Ret.Kind == TK.Unit) CheckEnsures(end, "true", f.EndSpan);
                break;
            case FnKind.Spec:
                CheckEnsures(s, T(f.BodyExpr!, SpecTx(s)), f.BodyExpr!.Span);
                break;
        }
        foreach (var h in _holes)
        {
            diags.Add(new Diagnostic
            {
                Code = "TN4001", Severity = "error", Message = $"hole ?{h.Hole.Name} has type {h.Hole.Type}",
                Hint = "Replace the hole with an expression of this type that meets the obligations listed.", FileIndex = h.Hole.Span.File,
                Line = h.Hole.Span.Line, Col = h.Hole.Span.Col, EndLine = h.Hole.Span.EndLine, EndCol = h.Hole.Span.EndCol,
                InScope = h.Scope, Facts = h.Facts, Obligations = h.Obligations,
            });
        }
        _holes.Clear();
    }

    // ---------- statements ----------

    /// <summary>Runs statements symbolically. Returns the merged state at the end, or null when every path returns.</summary>
    private State? Exec(List<Stmt> stmts, State? s)
    {
        foreach (var stmt in stmts)
        {
            if (s == null) return null;
            s = Exec(stmt, s);
        }
        return s;
    }

    private State? Exec(Stmt stmt, State s)
    {
        switch (stmt)
        {
            case Let l:
            {
                var v = T(l.Init, CodeTx(s, l.Ghost));
                if (l.Annotation?.Refine != null) ProveRefine(s, l.Annotation, v, l.Init.Span, $"'{l.Name}'");
                Bind(s, l.Name, v, l.VarType);
                if (!l.Mutable) s.Facts.Add($"{l.Name} == {Text(l.Init)}");
                return s;
            }
            case Set st:
            {
                var v = T(st.Value, CodeTx(s, st.Ghost));
                if (st.VarType.Refine != null) ProveRefine(s, st.VarType, v, st.Value.Span, $"'{st.Name}'");
                Bind(s, st.Name, v, s.Store[st.Name].Type);
                return s;
            }
            case Print p:
                T(p.Value, CodeTx(s, false));
                return s;
            case Do d:
                T(d.Call, CodeTx(s, d.Ghost));
                return s;
            case Assert a:
            {
                var cond = T(a.Cond, CodeTx(s, true));
                Prove(s, cond, "TN3003", $"assertion might not hold: {Text(a.Cond)}", a.Span,
                    "Strengthen a precondition or loop invariant, call a lemma, or fix the code so the assertion follows.");
                s.Path.Add(cond);
                s.Facts.Add(Text(a.Cond));
                return s;
            }
            case Return r:
                CheckEnsures(s, T(r.Value, CodeTx(s, false)), r.Span);
                return null;
            case If i:
            {
                var c = T(i.Cond, CodeTx(s, i.Ghost));
                var (n, nf) = (s.Path.Count, s.Facts.Count);
                var yes = s.Clone();
                yes.Path.Add(c);
                yes.Facts.Add(Text(i.Cond));
                s.Path.Add($"(not {c})");
                s.Facts.Add($"!({Text(i.Cond)})");
                return Join([Exec(i.Then, yes), i.Else == null ? s : Exec(i.Else, s)], n, nf);
            }
            case MatchStmt m:
            {
                var sc = T(m.Scrutinee, CodeTx(s, m.Ghost));
                var (n, nf) = (s.Path.Count, s.Facts.Count);
                var outs = new List<State?>();
                var earlier = new List<string>();
                foreach (var (p, body) in m.Arms)
                {
                    var st = s.Clone();
                    var cond = PatternCond(p, m.Scrutinee.Type, sc, earlier, CodeTx(s, m.Ghost));
                    st.Path.Add(cond);
                    st.Facts.Add($"{Text(m.Scrutinee)} is {PatternText(p)}");
                    if (p.Resolved != null)
                    {
                        var map = Checker.Map(p.Resolved.Owner.TypeParams, m.Scrutinee.Type.Args);
                        for (var k = 0; k < p.Binders.Count; k++)
                        {
                            if (p.Binders[k] == "_") continue;
                            var ft = p.Resolved.Fields[k].Type.Subst(map, new Dictionary<string, Dim>());
                            var term = $"(s.{p.Resolved.Name}.{p.Resolved.Fields[k].Name} {sc})";
                            Bind(st, p.Binders[k], term, ft);
                            Assume(st, ft, term);
                        }
                    }
                    outs.Add(Exec(body, st));
                }
                return Join(outs, n, nf);
            }
            case While w:
                return ExecWhile(w, s);
            case For fr:
                return ExecFor(fr, s);
            case Throw th:
            {
                var tx = CodeTx(s, false);
                var e = th.Value.Exception!;
                for (var i = 0; i < th.Value.Args.Count; i++)
                {
                    var v = T(th.Value.Args[i], tx);
                    if (e.Fields[i].Type.Refine != null) ProveRefine(s, e.Fields[i].Type, v, th.Value.Args[i].Span, $"field '{e.Fields[i].Name}' of '{e.Name}'");
                }
                ThrowAt(th.Site!, tx, null, th.Span);
                return null;
            }
            case Try t:
                return ExecTry(t, s);
            case Break:
                _loopsCtx.Peek().Breaks.Add(s);
                return null;
            case Continue:
                _loopsCtx.Peek().Continues.Add(s);
                return null;
            default:
                throw new InvalidOperationException();
        }
    }

    /// <summary>For each catch clause being verified: the states at the throw sites that may reach it.</summary>
    private readonly Dictionary<Catch, List<State?>> _catchStates = [];

    /// <summary>
    /// A catch body starts from the join of the states at every point in the try block that may throw its exception,
    /// as a loop exit joins the states at its 'break' statements. The exception's fields are arbitrary values of
    /// their types. After the statement, the end of the try block and the ends of the catch bodies join.
    /// </summary>
    private State? ExecTry(Try t, State s)
    {
        var (n, nf) = (s.Path.Count, s.Facts.Count);
        foreach (var c in t.Catches) _catchStates[c] = [];
        var outs = new List<State?> { Exec(t.Body, s) };
        foreach (var c in t.Catches)
        {
            var entry = Join(_catchStates[c], n, nf);
            _catchStates.Remove(c);
            if (entry == null) continue;
            entry.Facts.Add($"caught {c.Name}");
            for (var k = 0; k < c.Binders.Count; k++)
            {
                if (c.Binders[k] == "_") continue;
                var type = c.Decl!.Fields[k].Type;
                var sym = Fresh(type, c.Binders[k]);
                Bind(entry, c.Binders[k], sym, type);
                Assume(entry, type, sym);
            }
            outs.Add(Exec(c.Body, entry));
        }
        return Join(outs, n, nf);
    }

    /// <summary>
    /// An exception may be thrown here; <paramref name="cond"/> is the callee's 'when' condition (null: always possible).
    /// The current state goes to each catch that may receive it. If it can leave the function, the function's own
    /// 'throws' clauses must allow it: their 'when' conditions must hold, or, if none covers it, it must be impossible.
    /// </summary>
    private void ThrowAt(ThrowSite site, Tx tx, string? cond, Span span)
    {
        if (site.Catches.Count > 0)
        {
            var st = tx.S.Clone();
            foreach (var (binder, text) in tx.Ctx)
                if (!binder) st.Path.Add(text);
            if (cond != null) st.Path.Add(cond);
            foreach (var c in site.Catches)
                if (_catchStates.TryGetValue(c, out var into)) into.Add(st.Clone());
        }
        if (!site.Escapes) return;
        var e = site.Exception;
        var clauses = _cur.AllThrows.Where(c => c.Decl != null && c.Decl.Overlaps(e)).ToList();
        if (!clauses.Any(c => c.Decl!.Covers(e)))
        {
            if (cond != null)
                Oblige(tx, Not(cond), "TN3017", $"'{e.Name}' might escape '{_cur.Name}': {Text(site.Clause!.When!)} might hold here", span,
                    $"The callee throws '{e.Name}' only when its 'when' condition holds. Prove it false here (a guard or a precondition), catch '{e.Name}', or declare 'throws {e.Name}'.");
            return;
        }
        var guarded = clauses.Where(c => c.When != null).ToList();
        if (guarded.Count == 0) return;
        var whens = guarded.Select(c => T(c.When!, new Tx(tx.S, _cur.Throws.Contains(c) ? tx.S.Store : Inherited(_cur, tx.S.Store)) { Instantiate = true })).ToList();
        var goal = cond == null ? And(whens) : $"(=> {cond} {And(whens)})";
        Oblige(tx, goal, "TN3017", $"'{_cur.Name}' might throw '{e.Name}' when {string.Join(" && ", guarded.Select(c => Text(c.When!)))} does not hold", span,
            $"A 'throws {e.Name} when ...' clause promises callers that the exception only happens under that condition. Weaken the condition or guard the throw.");
    }

    /// <summary>The states that leave the innermost loop's body early, by 'break' or 'continue'.</summary>
    private sealed class LoopCtx
    {
        public List<State> Breaks { get; } = [];
        public List<State> Continues { get; } = [];
    }

    private readonly Stack<LoopCtx> _loopsCtx = new();

    /// <summary>The condition under which an arm matches. Arms are disjoint except '_', which takes what is left.</summary>
    private string PatternCond(Pattern p, TType scrutinee, string sc, List<string> earlier, Tx tx)
    {
        string Alt(Pattern a) => a.Resolved != null ? Tester(a.Resolved, scrutinee, sc, tx) : $"(= {sc} {T(a.Literal!, tx)})";
        if (p.IsWildcard) return Not(Or(earlier));
        var cond = p.Alternatives != null ? Or(p.Alternatives.Select(Alt).ToList()) : Alt(p);
        earlier.Add(cond);
        return cond;
    }

    private string PatternText(Pattern p) =>
        p.Alternatives != null ? string.Join(" | ", p.Alternatives.Select(PatternText))
        : p.Literal != null ? Text(p.Literal)
        : p.Case ?? "_";

    /// <summary>Runs one loop body: the normal end and every 'continue' join; 'break' states are returned separately.</summary>
    private (State? End, List<State> Breaks) ExecBody(List<Stmt> body, State start)
    {
        var ctx = new LoopCtx();
        _loopsCtx.Push(ctx);
        var n = (start.Path.Count, start.Facts.Count);
        var end = Exec(body, start);
        _loopsCtx.Pop();
        return (Join([end, .. ctx.Continues], n.Item1, n.Item2), ctx.Breaks);
    }

    /// <summary>
    /// 'for' loops: the bounds are evaluated once, the index counts up by one, and the loop variables cannot be
    /// assigned, so termination needs no proof. The index is known to stay between the bounds.
    /// </summary>
    private State? ExecFor(For fr, State s)
    {
        var tx = CodeTx(s, fr.Ghost);
        string lo, hi, array = "";
        if (fr.Source != null)
        {
            array = T(fr.Source, tx);
            var arr = $"for.a!{_fresh++}";
            Declare($"(declare-const {arr} {Sort(fr.Source.Type)})");
            s.Path.Add($"(= {arr} {array})");
            array = arr;
            (lo, hi) = ("0", $"(alen {arr})");
        }
        else
        {
            lo = T(fr.Lo!, tx);
            var h = T(fr.Hi!, tx);
            hi = $"for.hi!{_fresh++}";
            Declare($"(declare-const {hi} Int)");
            s.Path.Add($"(= {hi} {h})");
        }
        var index = fr.IndexName;
        Bind(s, index, lo, TType.Int);
        foreach (var inv in fr.Invariants)
            Prove(s, T(inv, new Tx(s, s.Store) { Instantiate = true }), "TN3004", $"loop invariant might not hold on entry: {Text(inv)}", inv.Span,
                "The invariant must be true before the first iteration, when the index is at its lower bound.");

        var assigned = new HashSet<string>();
        CollectAssigned(fr.Body, assigned);
        foreach (var name in assigned.Where(s.Store.ContainsKey).ToList())
        {
            var type = s.Store[name].Type;
            var sym = Fresh(type, name);
            Bind(s, name, sym, type);
            Assume(s, type, sym);
        }
        var i = Fresh(TType.Int, "for.i");
        Bind(s, index, i, TType.Int);
        s.Path.Add($"(and (<= {lo} {i}) (<= {i} (ite (<= {lo} {hi}) {hi} {lo})))");
        foreach (var inv in fr.Invariants)
        {
            s.Path.Add(T(inv, SpecTx(s)));
            s.Facts.Add(Text(inv));
        }
        var cond = $"(< {i} {hi})";
        var n = (s.Path.Count, s.Facts.Count);

        var body = s.Clone();
        body.Path.Add(cond);
        if (fr.Elem != null)
        {
            var elem = $"(select (elems {array}) {i})";
            Bind(body, fr.Elem, elem, fr.ElemType);
            Assume(body, fr.ElemType, elem);
            body.Facts.Add($"{fr.Elem} == {Text(fr.Source!)}[{index}]");
        }
        var (end, breaks) = ExecBody(fr.Body, body);
        if (end != null)
        {
            Bind(end, index, $"(+ {i} 1)", TType.Int);
            foreach (var inv in fr.Invariants)
                Prove(end, T(inv, new Tx(end, end.Store) { Instantiate = true }), "TN3005", $"loop invariant might not be maintained: {Text(inv)}", inv.Span,
                    "The invariant must hold again after every iteration, with the index advanced by one. The counterexample shows values at the end of one iteration.");
        }
        s.Path.Add($"(not {cond})");
        return Join([s, .. breaks], n.Item1, n.Item2);
    }

    /// <summary>Merges the states that reach a join point into one, so later statements are explored once.</summary>
    private State? Join(List<State?> states, int n, int nf)
    {
        var live = states.Where(x => x != null).Select(x => x!).ToList();
        if (live.Count <= 1) return live.FirstOrDefault();
        var j = new State { Path = live[0].Path.Take(n).ToList(), Facts = live[0].Facts.Take(nf).ToList() };
        var guards = new List<string>();
        foreach (var st in live)
        {
            var g = $"g!{_fresh++}";
            Declare($"(declare-const {g} Bool)");
            j.Path.Add($"(= {g} {And(st.Path.Skip(n).ToList())})");
            guards.Add(g);
        }
        j.Path.Add(Or(guards));
        foreach (var (name, (term, type)) in live[0].Store)
        {
            if (!live.All(st => st.Store.ContainsKey(name))) continue;
            var terms = live.Select(st => st.Store[name].Term).ToList();
            if (terms.All(t => t == term)) { j.Store[name] = (term, type); continue; }
            var sym = Fresh(type, name);
            for (var i = 0; i < live.Count; i++) j.Path.Add($"(=> {guards[i]} (= {sym} {terms[i]}))");
            j.Store[name] = (sym, type);
        }
        return j;
    }

    private State? ExecWhile(While w, State s)
    {
        foreach (var inv in w.Invariants)
            Prove(s, T(inv, new Tx(s, s.Store) { Instantiate = true }), "TN3004", $"loop invariant might not hold on entry: {Text(inv)}", inv.Span,
                "The invariant must be true before the first iteration. Weaken it or initialise the variables so it holds.");

        // Forget everything about the variables the loop assigns; only the invariants describe them from here on.
        var assigned = new HashSet<string>();
        CollectAssigned(w.Body, assigned);
        foreach (var name in assigned.Where(s.Store.ContainsKey).ToList())
        {
            var type = s.Store[name].Type;
            var sym = Fresh(type, name);
            Bind(s, name, sym, type);
            Assume(s, type, sym);
        }
        foreach (var inv in w.Invariants)
        {
            s.Path.Add(T(inv, SpecTx(s)));
            s.Facts.Add(Text(inv));
        }
        var measure = w.Decreases.Select(d => T(d, SpecTx(s))).ToList();
        var cond = T(w.Cond, CodeTx(s, w.Ghost));

        var body = s.Clone();
        body.Path.Add(cond);
        body.Facts.Add(Text(w.Cond));
        var n = (s.Path.Count, s.Facts.Count);
        var (end, breaks) = ExecBody(w.Body, body);
        if (end != null)
        {
            foreach (var inv in w.Invariants)
                Prove(end, T(inv, new Tx(end, end.Store) { Instantiate = true }), "TN3005", $"loop invariant might not be maintained: {Text(inv)}", inv.Span,
                    "The invariant must hold again after every iteration. The counterexample shows values at the end of one iteration.");
            if (measure.Count > 0)
            {
                var after = w.Decreases.Select(d => T(d, new Tx(end, end.Store) { Instantiate = true })).ToList();
                var text = string.Join(", ", w.Decreases.Select(Text));
                Prove(end, LexLess(after, measure), "TN3008",
                    $"loop might not terminate: '{text}' does not decrease{(measure.Count > 1 ? " lexicographically" : "")} on every iteration while staying non-negative",
                    w.Decreases[0].Span, "Every path through the loop body must make the 'decreases' measure strictly smaller, and it must not go below zero.");
            }
        }

        s.Path.Add(Not(cond));
        s.Facts.Add($"!({Text(w.Cond)})");
        return Join([s, .. breaks], n.Item1, n.Item2);
    }

    private static void CollectAssigned(List<Stmt> stmts, HashSet<string> into)
    {
        foreach (var stmt in stmts)
        {
            switch (stmt)
            {
                case Set st: into.Add(st.Name); break;
                case If i: CollectAssigned(i.Then, into); if (i.Else != null) CollectAssigned(i.Else, into); break;
                case While w: CollectAssigned(w.Body, into); break;
                case For f: CollectAssigned(f.Body, into); break;
                case MatchStmt m: foreach (var a in m.Arms) CollectAssigned(a.Body, into); break;
                case Try t:
                    CollectAssigned(t.Body, into);
                    foreach (var c in t.Catches) CollectAssigned(c.Body, into);
                    break;
            }
        }
    }

    private void CheckEnsures(State s, string resultTerm, Span span)
    {
        var st = s.Clone();
        st.Store["result"] = (resultTerm, _cur.Ret);
        if (_cur.Ret.Refine != null) ProveRefine(st, _cur.Ret, resultTerm, span, "the result");
        foreach (var e in _cur.Ensures)
            Prove(st, T(e, new Tx(st, st.Store) { Instantiate = true }), "TN3001", $"postcondition of '{_cur.Name}' might not hold: {Text(e)}", span,
                "Either the code returns a wrong value on this path, or the 'ensures' clause is too strong. The counterexample gives concrete inputs.");
        if (_cur.Implements is { } im)
            foreach (var e in im.Ensures)
                Prove(st, T(e, new Tx(st, Inherited(_cur, st.Store)) { Instantiate = true }), "TN3001",
                    $"'{_cur.Name}' might not meet the postcondition it inherits from '{im.Name}': {Text(e)}", span,
                    $"Code that calls '{im.Name}' relies on this clause, so every implementation must guarantee it.");
    }

    private static string LexLess(List<string> callee, List<string> caller)
    {
        var options = new List<string>();
        for (var k = 0; k < caller.Count && k < callee.Count; k++)
        {
            var conj = Enumerable.Range(0, k).Select(i => $"(= {callee[i]} {caller[i]})").ToList();
            conj.Add($"(< {callee[k]} {caller[k]})");
            conj.Add($"(>= {caller[k]} 0)");
            options.Add(And(conj));
        }
        return Or(options);
    }

    // ---------- refinements ----------

    private string? RefineFact(TType t, string term, Tx? ctx)
    {
        if (t.Refine == null) return null;
        var decl = t.Refine;
        var args = ctx == null || ctx.Types.Count == 0 ? t.RefineArgs : t.RefineArgs.Select(a => a.Subst(ctx.Types, new Dictionary<string, Dim>())).ToList();
        var sink = ctx?.S ?? new State();
        var env = new Dictionary<string, (string, TType)> { ["self"] = (term, decl.Base!) };
        return T(decl.Pred!, new Tx(sink, env) { Types = Checker.Map(decl.TypeParams, args) });
    }

    /// <summary>Records what is known about a value of type <paramref name="t"/>: its refinement and non-negative array length.</summary>
    private void Assume(State s, TType t, string term)
    {
        if (RefineFact(t, term, new Tx(s, s.Store)) is { } fact) s.Path.Add(fact);
        if (TypeFact(t, term) is { } wf) s.Path.Add(wf);
        // Every Int that exists at run time fits in 64 bits. Total mode proves operations stay in range, so it may
        // also assume inputs are in range; without it, a parameter could be a mathematical integer no caller can pass.
        if (_cur.Total && t.Kind == TK.Int) s.Path.Add(InRange(term));
    }

    private static string InRange(string term) => $"(and (<= {MinInt} {term}) (<= {term} {MaxInt}))";
    private static string InRange32(string term) => $"(and (<= {MinInt32} {term}) (<= {term} {MaxInt32}))";

    /// <summary>
    /// What holds of every run-time value of type <paramref name="t"/>, independent of contracts: a Date is a valid
    /// day, an Int32 fits in 32 bits, lengths and sizes are consistent. Arrays of such values get the fact per element.
    /// </summary>
    private string? TypeFact(TType t, string term)
    {
        switch (t.Kind)
        {
            case TK.Date: return $"(and (<= 0 {term}) (<= {term} {MaxDay}))";
            case TK.Int32: return InRange32(term);
            case TK.Map: return $"(and (>= (msize {term}) 0) (= (alen (mkeys {term})) (msize {term})))";
            case TK.Set: return $"(and (>= (ssize {term}) 0) (= (alen (sitems {term})) (ssize {term})))";
            case TK.Array:
            {
                var i = $"i!{_fresh++}";
                var elem = $"(select (elems {term}) {i})";
                _perElement++;
                var elemFact = TypeFact(t.Elem!, elem);
                _perElement--;
                if (elemFact is not { } ef) return $"(>= (alen {term}) 0)";
                var body = $"(=> (and (<= 0 {i}) (< {i} (alen {term}))) {ef})";
                return $"(and (>= (alen {term}) 0) (forall (({i} Int)) {Triggered(body, elem)}))";
            }
            case TK.Named when t.Decl is { Kind: not TypeKind.Refinement } decl && _factsOpen.Add(decl):
                try
                {
                    var map = Checker.Map(decl.TypeParams, t.Args);
                    List<string> FieldFacts(List<FieldDecl> fields, string owner) => fields
                        .Select(f => TypeFact(f.Type.Subst(map, new Dictionary<string, Dim>()), $"(s.{owner}.{f.Name} {term})"))
                        .OfType<string>().ToList();
                    static string All(List<string> facts) => facts.Count == 1 ? facts[0] : $"(and {string.Join(" ", facts)})";
                    if (decl.Kind == TypeKind.Record)
                    {
                        var facts = FieldFacts(decl.Fields, decl.Name);
                        // Sound because every construction proves the invariant (ProveInvariant) and values never change.
                        facts.AddRange(AssumedInvariant(decl, term));
                        return facts.Count == 0 ? null : All(facts);
                    }
                    var cases = decl.Cases
                        .Select(c => (Case: c, Facts: FieldFacts(c.Fields, c.Name)))
                        .Where(x => x.Facts.Count > 0)
                        .Select(x => $"(=> {Tester(x.Case, t, term)} {All(x.Facts)})")
                        .ToList();
                    return cases.Count == 0 ? null : All(cases);
                }
                finally
                {
                    _factsOpen.Remove(decl);
                }
            default: return null;
        }
    }

    /// <summary>Datatypes whose field facts are being built; a recursive type contributes facts one level deep.</summary>
    private readonly HashSet<TypeDecl> _factsOpen = [];

    /// <summary>Records the type facts of a value read from somewhere opaque (a field, an element, a builtin result).</summary>
    private void Known(Tx tx, TType t, string term)
    {
        if (TypeFact(t, term) is { } f) AddFact(tx, f);
    }

    private void ProveRefine(State s, TType t, string term, Span span, string what)
    {
        var fact = RefineFact(t, term, new Tx(s, s.Store))!;
        Prove(s, fact, "TN3014", $"{what} might not satisfy refinement type {t}: {Text(t.Refine!.Pred!)}", span,
            $"Every value of type {t.Refine!.Name} must satisfy its 'where' clause. Establish it before this point.");
    }

    // ---------- expressions ----------

    private string T(Expr e, Tx tx)
    {
        var term = TCore(e, tx);
        if (e.Upcast != null) term = $"({Up(e.Type.Decl!, e.Upcast)} {term})";
        if (tx.Checks)
            foreach (var (a, b) in e.ShapeEqs)
                Oblige(tx, $"(= {DimT(a, tx)} {DimT(b, tx)})", "TN3012", $"tensor dimensions might differ: {a} vs {b}", e.Span,
                    "The shapes only match if these dimensions are equal. Add a precondition relating the dimension parameters.");
        return term;
    }

    private string TCore(Expr e, Tx tx)
    {
        switch (e)
        {
            case IntLit i: return i.Type.Kind == TK.Decimal ? $"{i.Value}.0" : i.Value.ToString();
            case FloatLit f: return FpLit(f.Value);
            case DecLit d: return DecimalLit(d.Value);
            case StrLit s: return StrLitSmt(s.Value);
            case Interp ip:
            {
                var parts = ip.Parts.Select(p => p is StrLit sl ? StrLitSmt(sl.Value) : ToStr(T(p, tx), p.Type)).ToList();
                return parts.Count == 1 ? parts[0] : $"(str.++ {string.Join(" ", parts)})";
            }
            case BoolLit b: return b.Value ? "true" : "false";
            case UnitLit: return "true";
            case Var { Kind: VarKind.Ctor } v: return Ctor(v.Ctor!, [], v.Type, tx);
            case Var { Kind: VarKind.Const } v:
            {
                // Constants are inlined; their obligations were proved once, where they are declared.
                var term = T(v.Const!.Value, NoChecks(tx));
                if (tx.Instantiate && RefineFact(v.Const.Type, term, tx) is { } fact) AddFact(tx, fact);
                return term;
            }
            case Var v: return tx.Bound.TryGetValue(v.Name, out var bound) ? bound : tx.Env[v.Name].Term;
            case Unary { Op: "!" } u: return Not(T(u.Operand, tx));
            case Unary u when u.Type.Kind == TK.Float: return $"(fp.neg {T(u.Operand, tx)})";
            case Unary u when u.Type.Kind == TK.Decimal: return $"(- {T(u.Operand, tx)})";
            case Unary u: return Overflow(tx, $"(- {T(u.Operand, tx)})", u);
            case WithExpr w:
            {
                var target = T(w.Target, tx);
                var decl = w.Target.Type.Decl!;
                var map = Checker.Map(decl.TypeParams, w.Target.Type.Args);
                var args = decl.Fields.Select(f => $"(s.{decl.Name}.{f.Name} {target})").ToList();
                for (var k = 0; k < w.Updates.Count; k++)
                {
                    var field = w.Resolved[k]!;
                    var value = T(w.Updates[k].Value, tx);
                    args[field.Index] = value;
                    var ft = field.Type.Subst(map, new Dictionary<string, Dim>());
                    if (ft.Refine != null)
                        Oblige(tx, RefineFact(ft, value, tx)!, "TN3014", $"field '{field.Name}' might not satisfy refinement type {ft}: {Text(ft.Refine.Pred!)}",
                            w.Updates[k].Value.Span, $"Every value of type {ft.Refine.Name} must satisfy its 'where' clause.");
                }
                var updated = Ctor(null, args, w.Type, tx, decl);
                ProveInvariant(tx, decl, updated, w.Span);
                return updated;
            }
            case Binary b: return TBinary(b, tx);
            case IfExpr i:
            {
                var c = T(i.Cond, tx);
                var t = Guarded(tx, c, () => T(i.Then, tx));
                var f = Guarded(tx, Not(c), () => T(i.Else, tx));
                return $"(ite {c} {t} {f})";
            }
            case Index ix:
            {
                var (a, at) = (T(ix.Array, tx), T(ix.At, tx));
                Oblige(tx, InBounds(a, at), "TN3007", $"index might be out of bounds: {Text(ix)}", ix.Span,
                    "Prove 0 <= index < len(array): add a precondition, a loop invariant, or a guard.");
                var elem = $"(select (elems {a}) {at})";
                if (tx.Exec && _cur.Total && ix.Type.Kind == TK.Int) AddFact(tx, InRange(elem));
                if (tx.Instantiate) Known(tx, ix.Type, elem);
                return elem;
            }
            case FieldAccess fa:
            {
                var term = $"(s.{fa.Target.Type.Name}.{fa.Field} {T(fa.Target, tx)})";
                var ft = fa.Resolved!.Type.Subst(Checker.Map(fa.Target.Type.Decl!.TypeParams, fa.Target.Type.Args), new Dictionary<string, Dim>());
                if (tx.Instantiate && RefineFact(ft, term, tx) is { } fact) AddFact(tx, fact);
                if (tx.Exec && _cur.Total && ft.Kind == TK.Int) AddFact(tx, InRange(term));
                if (tx.Instantiate) Known(tx, ft, term);
                return term;
            }
            case ArrayLit a:
            {
                var sort = Sort(a.Type.Elem!, tx);
                var arr = $"a!{_fresh++}";
                Declare($"(declare-const {arr} (Array Int {sort}))");
                var elems = arr;
                for (var k = 0; k < a.Elems.Count; k++) elems = $"(store {elems} {k} {T(a.Elems[k], tx)})";
                return $"(mk {elems} {a.Elems.Count})";
            }
            case TensorLit t:
            {
                var sym = Fresh(t.Type, "tensor");
                if (tx.Instantiate)
                    for (var k = 0; k < t.Values.Count; k++)
                        tx.S.Path.Add($"(= (el {sym} {k}) {RealLit(t.Elem == ElemType.Float32 ? (float)t.Values[k] : t.Values[k])})");
                return sym;
            }
            case Quant q: return TQuant(q, tx);
            case MatchExpr m: return TMatch(m, tx);
            case Hole h:
            {
                var sym = Fresh(h.Type, $"hole.{h.Name}");
                _holes.Add(new HoleInfo
                {
                    Hole = h, Sym = sym, Facts = [.. tx.S.Facts],
                    Scope = tx.Env.Where(kv => kv.Key != "result").ToDictionary(kv => kv.Key, kv => kv.Value.Type.ToString()),
                });
                return sym;
            }
            case Call c: return TCall(c, tx);
            default: throw new InvalidOperationException(e.GetType().Name);
        }
    }

    private string TBinary(Binary b, Tx tx)
    {
        var l = T(b.Left, tx);
        switch (b.Op)
        {
            case "&&": return $"(and {l} {Guarded(tx, l, () => T(b.Right, tx))})";
            case "||": return $"(or {l} {Guarded(tx, Not(l), () => T(b.Right, tx))})";
            case "==>": return $"(=> {l} {Guarded(tx, l, () => T(b.Right, tx))})";
        }
        var isFloat = b.Left.Type.Kind == TK.Float;
        if (isFloat && (b.Left.RealModel || b.Right.RealModel) && b.Op is not ("+" or "-" or "*" or "/"))
        {
            var (rl, rr) = (TReal(b.Left, tx), TReal(b.Right, tx));
            return b.Op switch { "==" => $"(= {rl} {rr})", "!=" => $"(not (= {rl} {rr}))", _ => $"({b.Op} {rl} {rr})" };
        }
        var r = T(b.Right, tx);
        switch (b.Left.Type.Kind)
        {
            case TK.String:
                return b.Op switch { "+" => $"(str.++ {l} {r})", "==" => $"(= {l} {r})", _ => $"(not (= {l} {r}))" };
            case TK.Decimal:
                // Decimal arithmetic is exact rational arithmetic here. At run time, results beyond 28-29 significant
                // digits are rounded (and beyond about 7.9e28, overflow traps): a documented, trusted approximation.
                switch (b.Op)
                {
                    case "/":
                        Oblige(tx, $"(not (= {r} 0.0))", "TN3006", $"possible division by zero: {Text(b)}", b.Span,
                            "Prove the divisor is non-zero: add a precondition or a guard.");
                        return $"(/ {l} {r})";
                    case "==": return $"(= {l} {r})";
                    case "!=": return $"(not (= {l} {r}))";
                    default: return $"({b.Op} {l} {r})";
                }
        }
        if (isFloat)
        {
            return b.Op switch
            {
                "+" => $"(fp.add RNE {l} {r})",
                "-" => $"(fp.sub RNE {l} {r})",
                "*" => $"(fp.mul RNE {l} {r})",
                "/" => $"(fp.div RNE {l} {r})",
                "==" => $"(fp.eq {l} {r})",
                "!=" => $"(not (fp.eq {l} {r}))",
                "<" => $"(fp.lt {l} {r})",
                "<=" => $"(fp.leq {l} {r})",
                ">" => $"(fp.gt {l} {r})",
                _ => $"(fp.geq {l} {r})",
            };
        }
        switch (b.Op)
        {
            case "/" or "%":
                Oblige(tx, $"(not (= {r} 0))", "TN3006", $"possible division by zero: {Text(b)}", b.Span,
                    "Prove the divisor is non-zero: add a precondition or a guard.");
                if (tx.Exec && _cur.Total)
                    Oblige(tx, $"(not (and (= {l} {(b.Left.Type.Kind == TK.Int32 ? MinInt32 : MinInt)}) (= {r} (- 1))))", "TN3011", $"integer overflow possible: {Text(b)}", b.Span,
                        $"Dividing the smallest {b.Left.Type.Base} by -1 overflows. Prove the operands avoid that case.");
                return $"({(b.Op == "/" ? "tdiv" : "tmod")} {l} {r})";
            case "+" or "-" or "*": return Overflow(tx, $"({b.Op} {l} {r})", b);
            case "==": return $"(= {l} {r})";
            case "!=": return $"(not (= {l} {r}))";
            default: return $"({b.Op} {l} {r})";
        }
    }

    private string Overflow(Tx tx, string term, Expr at)
    {
        if (tx.Exec && _cur.Total && at.Type.Kind == TK.Int32)
            Oblige(tx, InRange32(term), "TN3011", $"integer overflow possible: {Text(at)}", at.Span,
                "In a 'total' function every Int32 operation must stay within 32 bits. Bound the operands with preconditions or invariants.");
        else if (tx.Exec && _cur.Total)
            Oblige(tx, $"(and (<= {MinInt} {term}) (<= {term} {MaxInt}))", "TN3011", $"integer overflow possible: {Text(at)}", at.Span,
                "In a 'total' function every Int operation must stay within 64 bits. Bound the operands with preconditions or invariants.");
        return term;
    }

    /// <summary>The same translation context without obligations, for re-translating an expression already checked.</summary>
    private static Tx NoChecks(Tx tx)
    {
        var t = new Tx(tx.S, tx.Env) { Instantiate = tx.Instantiate, Exec = tx.Exec, Types = tx.Types };
        t.Ctx.AddRange(tx.Ctx);
        foreach (var (k, v) in tx.Bound) t.Bound[k] = v;
        return t;
    }

    /// <summary>An SMT-LIB string literal: quotes doubled, everything outside printable ASCII as \u{...}.</summary>
    private static string StrLitSmt(string s)
    {
        var sb = new StringBuilder("\"");
        foreach (var c in s)
        {
            if (c == '"') sb.Append("\"\"");
            else if (c < 0x20 || c > 0x7e || c == '\\') sb.Append($"\\u{{{(int)c:x}}}");
            else sb.Append(c);
        }
        return sb.Append('"').ToString();
    }

    /// <summary>The exact rational value of a decimal.</summary>
    private static string DecimalLit(decimal d)
    {
        var bits = decimal.GetBits(d);
        var scale = (bits[3] >> 16) & 0xFF;
        var mantissa = new BigInteger((uint)bits[0]) | (new BigInteger((uint)bits[1]) << 32) | (new BigInteger((uint)bits[2]) << 64);
        var den = BigInteger.Pow(10, scale);
        var g = BigInteger.GreatestCommonDivisor(mantissa, den);
        if (!g.IsZero) (mantissa, den) = (mantissa / g, den / g);
        var r = den.IsOne ? $"{mantissa}.0" : $"(/ {mantissa}.0 {den}.0)";
        return d < 0 ? $"(- {r})" : r;
    }

    /// <summary>The text of a value, as 'to_str' and string interpolation produce it.</summary>
    private static string ToStr(string term, TType t) => t.Kind switch
    {
        TK.String => term,
        TK.Int or TK.Int32 => $"(s.int {term})",
        TK.Bool => $"(ite {term} \"true\" \"false\")",
        TK.Decimal => $"(s.dec {term})",
        TK.Date => $"(s.date {term})",
        _ => throw new InvalidOperationException(t.ToString()),
    };

    /// <summary>A Float expression in the real-number tensor model.</summary>
    private string TReal(Expr e, Tx tx) => e switch
    {
        FloatLit f => RealLit(f.Value),
        Var { Kind: VarKind.Elem } v => tx.Bound[v.Name],
        Unary u => $"(- {TReal(u.Operand, tx)})",
        Binary b when b.Op is "+" or "-" or "*" or "/" => $"({b.Op} {TReal(b.Left, tx)} {TReal(b.Right, tx)})",
        Call { Name: "row_sum", IsBuiltin: true } => T(e, tx),
        _ => $"(fp.to_real {T(e, tx)})",
    };

    private string TQuant(Quant q, Tx tx)
    {
        switch (q.Kind)
        {
            case QuantKind.Range:
            {
                var (lo, hi) = (T(q.Lo!, tx), T(q.Hi!, tx));
                var sym = $"q.{q.Binders[0].Name}!{_fresh++}";
                var range = $"(and (<= {lo} {sym}) (< {sym} {hi}))";
                var body = Bind1(tx, q.Binders[0].Name, sym, "Int", range, () => T(q.Body, tx));
                return q.ForAll ? $"(forall (({sym} Int)) (=> {range} {body}))" : $"(exists (({sym} Int)) (and {range} {body}))";
            }
            case QuantKind.Elems:
            {
                var t = T(q.Source!, tx);
                var i = $"i!{_fresh++}";
                var range = $"(and (<= 0 {i}) (< {i} {SizeTerm(q.Source!.Type, tx)}))";
                tx.Ctx.Add((true, $"({i} Int)"));
                tx.Bound[q.Binders[0].Name] = $"(el {t} {i})";
                var body = Guarded(tx, range, () => T(q.Body, tx));
                tx.Bound.Remove(q.Binders[0].Name);
                tx.Ctx.RemoveAt(tx.Ctx.Count - 1);
                return q.ForAll ? $"(forall (({i} Int)) (=> {range} {body}))" : $"(exists (({i} Int)) (and {range} {body}))";
            }
            default:
            {
                var syms = q.Binders.Select(b => (b.Name, Sym: $"q.{b.Name}!{_fresh++}", Sort: Sort(b.Type, tx), b.Type)).ToList();
                foreach (var b in syms)
                {
                    tx.Bound[b.Name] = b.Sym;
                    tx.Ctx.Add((true, $"({b.Sym} {b.Sort})"));
                }
                var guards = syms.Select(b => RefineFact(b.Type, b.Sym, tx)).Where(g => g != null).Select(g => g!).ToList();
                if (syms.Any(b => b.Type.Kind == TK.Array)) guards.AddRange(syms.Where(b => b.Type.Kind == TK.Array).Select(b => $"(>= (alen {b.Sym}) 0)"));
                _perElement++;
                foreach (var b in syms.Where(b => b.Type.IsClass)) guards.AddRange(AssumedInvariant(b.Type.Decl!, b.Sym));
                _perElement--;
                var guard = And(guards);
                var body = Guarded(tx, guard, () => T(q.Body, tx));
                var patterns = new List<string>();
                foreach (var group in q.Triggers)
                {
                    var ptx = new Tx(tx.S, tx.Env) { Types = tx.Types };
                    foreach (var (k, v) in tx.Bound) ptx.Bound[k] = v;
                    var terms = string.Join(" ", group.Select(t => T(t, ptx)));
                    if (!Unpatternable.IsMatch(terms)) patterns.Add($":pattern ({terms})");
                }
                foreach (var b in syms) tx.Bound.Remove(b.Name);
                tx.Ctx.RemoveRange(tx.Ctx.Count - syms.Count, syms.Count);
                var binders = string.Join(" ", syms.Select(b => $"({b.Sym} {b.Sort})"));
                var inner = q.ForAll ? $"(=> {guard} {body})" : $"(and {guard} {body})";
                var annotated = patterns.Count == 0 ? inner : $"(! {inner} {string.Join(" ", patterns)})";
                return $"({(q.ForAll ? "forall" : "exists")} ({binders}) {annotated})";
            }
        }
    }

    private string Bind1(Tx tx, string name, string sym, string sort, string guard, Func<string> inner)
    {
        tx.Bound[name] = sym;
        tx.Ctx.Add((true, $"({sym} {sort})"));
        var r = Guarded(tx, guard, inner);
        tx.Ctx.RemoveAt(tx.Ctx.Count - 1);
        tx.Bound.Remove(name);
        return r;
    }

    private string TMatch(MatchExpr m, Tx tx)
    {
        var sc = T(m.Scrutinee, tx);
        var arms = new List<(string Cond, string Body)>();
        var earlier = new List<string>();
        foreach (var (p, body) in m.Arms)
        {
            var cond = PatternCond(p, m.Scrutinee.Type, sc, earlier, tx);
            var bound = new List<string>();
            if (p.Resolved != null)
            {
                var map = Checker.Map(p.Resolved.Owner.TypeParams, m.Scrutinee.Type.Args);
                for (var k = 0; k < p.Binders.Count; k++)
                {
                    if (p.Binders[k] == "_") continue;
                    var field = p.Resolved.Fields[k];
                    var term = $"(s.{p.Resolved.Name}.{field.Name} {sc})";
                    tx.Bound[p.Binders[k]] = term;
                    bound.Add(p.Binders[k]);
                    if (tx.Instantiate && RefineFact(field.Type.Subst(map, new Dictionary<string, Dim>()), term, tx) is { } fact)
                        AddFact(tx, $"(=> {cond} {fact})");
                }
            }
            arms.Add((cond, Guarded(tx, cond, () => T(body, tx))));
            foreach (var b in bound) tx.Bound.Remove(b);
        }
        var result = arms[^1].Body;
        for (var k = arms.Count - 2; k >= 0; k--) result = $"(ite {arms[k].Cond} {arms[k].Body} {result})";
        return result;
    }

    /// <summary>'term is case c'. Testers of parametric datatypes need the full instantiated signature to be unambiguous.</summary>
    private string Tester(CaseDecl c, TType type, string term, Tx? tx = null)
    {
        if (c.Owner.TypeParams.Count == 0) return $"((_ is c.{c.Name}) {term})";
        var map = Checker.Map(c.Owner.TypeParams, type.Args);
        var fields = c.Fields.Select(f => Sort(f.Type.Subst(map, new Dictionary<string, Dim>()), tx));
        return $"((_ is (c.{c.Name} ({string.Join(" ", fields)}) {Sort(type, tx)})) {term})";
    }

    private string Ctor(CaseDecl? c, List<string> args, TType type, Tx tx, TypeDecl? record = null)
    {
        var name = c?.Name ?? record!.Name;
        var owner = c?.Owner ?? record!;
        var sort = Sort(type, tx);
        if (owner.TypeParams.Count == 0) return args.Count == 0 ? $"c.{name}" : $"(c.{name} {string.Join(" ", args)})";
        return args.Count == 0 ? $"(as c.{name} {sort})" : $"((as c.{name} {sort}) {string.Join(" ", args)})";
    }

    private string TCall(Call c, Tx tx)
    {
        if (c.IsBuiltin && Checker.LambdaBuiltins.Contains(c.Name)) return TLambdaBuiltin(c, tx);
        var args = c.Args.Select(a => T(a, tx)).ToList();
        if (c.Case != null || c.Record != null)
        {
            var fields = c.Case?.Fields ?? c.Record!.Fields;
            var owner = c.Case?.Owner ?? c.Record!;
            var map = c.Type.IsError ? [] : Checker.Map(owner.TypeParams, c.Type.Args);
            if (tx.Checks)
                for (var i = 0; i < fields.Count; i++)
                {
                    var ft = fields[i].Type.Subst(map, new Dictionary<string, Dim>());
                    if (ft.Refine != null)
                        Oblige(tx, RefineFact(ft, args[i], tx)!, "TN3014", $"field '{fields[i].Name}' of '{c.Name}' might not satisfy refinement type {ft}: {Text(ft.Refine.Pred!)}",
                            c.Args[i].Span, $"Every value of type {ft.Refine.Name} must satisfy its 'where' clause.");
                }
            var built = Ctor(c.Case, args, c.Type, tx, c.Record);
            if (c.Record != null) ProveInvariant(tx, c.Record, built, c.Span);
            return built;
        }
        if (c.Target == null) return TBuiltin(c, args, tx);

        // The callee's contract is read with its parameters replaced by the argument terms. Applications nested
        // inside that contract are left uninterpreted, which bounds instantiation depth and keeps queries predictable.
        var f = c.Target;
        var types = c.TypeArgs.ToDictionary(kv => kv.Key, kv => tx.Types.Count == 0 ? kv.Value : kv.Value.Subst(tx.Types, new Dictionary<string, Dim>()));
        var dimTerms = f.DimParams.Select(d => DimT(c.DimArgs[d], tx)).ToList();
        var env = new Dictionary<string, (string, TType)>();
        for (var i = 0; i < f.DimParams.Count; i++) env[f.DimParams[i]] = (dimTerms[i], TType.Int);
        for (var i = 0; i < args.Count; i++) env[f.Params[i].Name] = (args[i], f.Params[i].Type);
        var spec = new Tx(tx.S, env) { Types = types };
        // An implementation's contract includes the one it inherits from its interface method.
        var inherited = f.Implements != null ? new Tx(tx.S, Inherited(f, env)) : null;
        var requires = f.Requires.Select(r => (Expr: r, Tx: spec)).Concat(inherited == null ? [] : f.Implements!.Requires.Select(r => (Expr: r, Tx: inherited))).ToList();
        var pres = requires.Select(r => T(r.Expr, r.Tx)).ToList();
        var refinePres = f.Params.Select((p, i) => (p, i, fact: RefineFact(p.Type, args[i], spec))).Where(x => x.fact != null).ToList();

        if (tx.Checks)
        {
            for (var i = 0; i < pres.Count; i++)
                Oblige(tx, pres[i], "TN3002", $"precondition of '{f.Name}' might not hold: {Text(requires[i].Expr)}", c.Span,
                    $"The caller must establish every 'requires' clause of '{f.Name}' before the call.");
            foreach (var (p, i, fact) in refinePres)
                Oblige(tx, fact!, "TN3014", $"argument '{p.Name}' of '{f.Name}' might not satisfy refinement type {p.Type}: {Text(p.Type.Refine!.Pred!)}",
                    c.Args[i].Span, $"Every value of type {p.Type.Refine!.Name} must satisfy its 'where' clause.");
            if (f.Recursive && f.Scc == _cur.Scc)
            {
                if (_measure == null)
                    diags.Error("TN2013", c.Span, $"'{f.Name}' is recursive with '{_cur.Name}' and cannot be called from its 'requires' or 'decreases' clause");
                else
                {
                    var callee = f.Decreases.Select(d => T(d, spec)).ToList();
                    Oblige(tx, LexLess(callee, _measure), "TN3008",
                        $"recursion might not terminate: the 'decreases' measure of '{f.Name}' must be smaller on this call than '{string.Join(", ", _cur.Decreases.Select(Text))}' here, and non-negative",
                        c.Span, "Guard the recursive call so the measure is >= 0 and strictly smaller (lexicographically) for the callee.");
                }
            }
            foreach (var site in c.ThrowSites)
            {
                var when = site.Clause!.When;
                var cond = when == null ? null : T(when, f.Throws.Contains(site.Clause) ? spec : inherited!);
                ThrowAt(site, tx, cond, c.Span);
            }
        }

        string result;
        if (f.Ret.Kind == TK.Unit) result = "true";
        else if (!f.IsPure) result = Fresh(f.Ret.Subst(types, new Dictionary<string, Dim>()), f.Name);
        else
        {
            var all = dimTerms.Concat(args).ToList();
            var sym = FnSym(f, types);
            result = all.Count == 0 ? sym : $"({sym} {string.Join(" ", all)})";
        }

        if (tx.Instantiate)
        {
            env["result"] = (result, f.Ret);
            var posts = f.Ensures.Select(e => T(e, spec)).ToList();
            if (inherited != null)
            {
                inherited.Env["result"] = (result, f.Ret);
                posts.AddRange(f.Implements!.Ensures.Select(e => T(e, inherited)));
            }
            if (RefineFact(f.Ret, result, spec) is { } rf) posts.Add(rf);
            if (TypeFact(f.Ret.Subst(types, new Dictionary<string, Dim>()), result) is { } wf) posts.Add(wf);
            if (_cur.Total && f.Ret.Kind == TK.Int && f.IsExecutable) posts.Add(InRange(result));
            if (f.Kind == FnKind.Spec) posts.Add($"(= {result} {T(f.BodyExpr!, spec)})");
            if (posts.Count > 0)
                AddFact(tx, $"(=> {And([.. pres, .. refinePres.Select(x => x.fact!)])} {And(posts)})");
        }
        return result;
    }

    private string TBuiltin(Call c, List<string> a, Tx tx)
    {
        void Bounds(string arr, string idx, Expr at) =>
            Oblige(tx, InBounds(arr, idx), "TN3007", $"index might be out of bounds: {Text(at)}", at.Span,
                "Prove 0 <= index < len(array): add a precondition, a loop invariant, or a guard.");
        switch (c.Name)
        {
            case "len": return $"(alen {a[0]})";
            case "update":
                Bounds(a[0], a[1], c);
                return $"(mk (store (elems {a[0]}) {a[1]} {a[2]}) (alen {a[0]}))";
            case "fill":
                Oblige(tx, $"(>= {a[0]} 0)", "TN3010", $"array length might be negative: {Text(c)}", c.Span, "Prove the length passed to 'fill' is >= 0.");
                return $"(mk ((as const (Array Int {Sort(c.Type.Elem!, tx)})) {a[1]}) {a[0]})";
            case "to_float": return $"((_ to_fp 11 53) RNE (to_real {a[0]}))";
            case "trunc":
            {
                // trunc(x) fits in 64 bits exactly when -2^63 <= x < 2^63 (both bounds are doubles). Staying in the
                // floating-point and bit-vector theories keeps these queries cheap; NaN and infinities fail the comparisons.
                Oblige(tx, $"(and (fp.lt {a[0]} {FpLit(9223372036854775808.0)}) (fp.geq {a[0]} {FpLit(-9223372036854775808.0)}))",
                    "TN3013", $"conversion to Int might fail: {Text(c)}", c.Span, "Prove the value is a number whose integer part fits in 64 bits.");
                var bv = $"((_ fp.to_sbv 64) RTZ {a[0]})";
                return $"(ite (bvslt {bv} #x0000000000000000) (- (bv2int {bv}) 18446744073709551616) (bv2int {bv}))";
            }
            case "row_sum":
                Oblige(tx, $"(and (<= 0 {a[1]}) (< {a[1]} {DimT(c.Args[0].Type.Dims[0], tx)}))", "TN3007", $"row index might be out of bounds: {Text(c)}", c.Span,
                    "Prove 0 <= row < the number of rows.");
                return $"(row_sum {a[0]} {a[1]})";
            case { } when TLibrary(c, a, tx) is { } lib:
                return lib;
            case "reshape" or "full":
            {
                var dims = c.Type.Dims.Select(d => DimT(d, tx)).ToList();
                var sym = $"tf.{c.Name}.r{dims.Count}";
                Declare($"(declare-fun {sym} ({string.Join(" ", dims.Select(_ => "Int"))} {(c.Name == "full" ? "F64" : "Tensor")}) Tensor)");
                var term = $"({sym} {string.Join(" ", dims)} {a[0]})";
                ElemAxioms(c, term, a, tx);
                return term;
            }
            default:
            {
                var term = $"(tf.{c.Name} {string.Join(" ", a)})";
                if (c.Type.Kind == TK.Tensor) ElemAxioms(c, term, a, tx);
                return term;
            }
        }
    }

    // ---------- library builtins ----------

    private TypeDecl OptionDecl => module.Types.First(t => t.Name == "Option" && t.Prelude);
    private CaseDecl SomeCase => OptionDecl.Cases.First(c => c.Name == "Some");
    private CaseDecl NoneCase => OptionDecl.Cases.First(c => c.Name == "None");
    private TType OptionOf(TType t) => TType.Named(OptionDecl, [t]);
    private string SomeOf(TType t, string v, Tx tx) => Ctor(SomeCase, [v], OptionOf(t), tx);
    private string NoneOf(TType t, Tx tx) => Ctor(NoneCase, [], OptionOf(t), tx);
    private string IsSome(TType t, string o, Tx tx) => Tester(SomeCase, OptionOf(t), o, tx);
    private static string ValueOf(string o) => $"(s.Some.value {o})";

    /// <summary>
    /// A fresh value that may depend on the enclosing quantifier binders: inside 'forall i', a value computed from
    /// i must be a function of i, or one constant would have to serve every i.
    /// </summary>
    private string FreshIn(Tx tx, TType type, string hint) => FreshFn(tx, [], Sort(type, tx), hint)([]);

    private Func<string[], string> FreshFn(Tx tx, string[] argSorts, string sort, string hint)
    {
        var binders = tx.Ctx.Where(c => c.Binder).Select(c =>
        {
            var inner = c.Text[1..^1];
            var k = inner.IndexOf(' ');
            return (Sym: inner[..k], Sort: inner[(k + 1)..]);
        }).ToList();
        var name = $"{hint}!{_fresh++}";
        var sorts = binders.Select(b => b.Sort).Concat(argSorts).ToList();
        Declare(sorts.Count == 0 ? $"(declare-const {name} {sort})" : $"(declare-fun {name} ({string.Join(" ", sorts)}) {sort})");
        return args =>
        {
            var all = binders.Select(b => b.Sym).Concat(args).ToList();
            return all.Count == 0 ? name : $"({name} {string.Join(" ", all)})";
        };
    }

    /// <summary>Replaces a generated symbol (such as i!12, never i!123) in a term.</summary>
    private static string Replace(string term, string sym, string with) =>
        Regex.Replace(term, Regex.Escape(sym) + @"(?![0-9])", with.Replace("$", "$$"));

    private static string Pow2(string k, int max = 62)
    {
        if (long.TryParse(k, out var lit) && lit is >= 0 and <= 62) return (1L << (int)lit).ToString();
        var t = (1L << max).ToString();
        for (var b = max - 1; b >= 0; b--) t = $"(ite (= {k} {b}) {1L << b} {t})";
        return t;
    }

    /// <summary>Strings, numbers, dates, arrays, maps, sets and options. Null when <paramref name="c"/> is not one of these.</summary>
    private string? TLibrary(Call c, List<string> a, Tx tx)
    {
        string Fact(string term, string fact)
        {
            if (tx.Instantiate) AddFact(tx, fact);
            return term;
        }
        TType ArgT(int i) => c.Args[i].Type;
        switch (c.Name)
        {
            case "str_len": return $"(str.len {a[0]})";
            case "str_sub":
                Oblige(tx, $"(and (<= 0 {a[1]}) (<= 0 {a[2]}) (<= (+ {a[1]} {a[2]}) (str.len {a[0]})))", "TN3007",
                    $"substring might be out of bounds: {Text(c)}", c.Span, "Prove 0 <= start, 0 <= length and start + length <= str_len(s).");
                return $"(str.substr {a[0]} {a[1]} {a[2]})";
            case "str_index_of": return $"(str.indexof {a[0]} {a[1]} 0)";
            case "str_contains": return $"(str.contains {a[0]} {a[1]})";
            case "str_starts_with": return $"(str.prefixof {a[1]} {a[0]})";
            case "str_ends_with": return $"(str.suffixof {a[1]} {a[0]})";
            case "str_trim":
            {
                var r = $"(s.trim {a[0]})";
                return Fact(r, $"(and (<= (str.len {r}) (str.len {a[0]})) (str.contains {a[0]} {r}))");
            }
            case "str_upper" or "str_lower":
            {
                var r = $"(s.{c.Name[4..]} {a[0]})";
                return Fact(r, $"(= (str.len {r}) (str.len {a[0]}))");
            }
            case "str_split":
            {
                var r = $"(s.split {a[0]} {a[1]})";
                return Fact(r, $"(>= (alen {r}) 1)");
            }
            case "str_join": return $"(s.join {a[0]} {a[1]})";
            case "str_eq_ignore_case": return $"(= (s.upper {a[0]}) (s.upper {a[1]}))";
            case "str_is_blank": return $"(= (s.trim {a[0]}) \"\")";
            case "to_str":
            {
                var r = ToStr(a[0], ArgT(0));
                return ArgT(0).Kind == TK.Date ? Fact(r, $"(= (str.len {r}) 10)") : r;
            }
            case "parse_int":
            {
                // A string of at most 18 digits parses to its value; anything else is left open.
                var r = $"(s.parse_int {a[0]})";
                return Fact(r, $"(=> (and (>= (str.to_int {a[0]}) 0) (<= (str.len {a[0]}) 18)) (= {r} {SomeOf(TType.Int, $"(str.to_int {a[0]})", tx)}))");
            }
            case "parse_decimal": return $"(s.parse_dec {a[0]})";
            case "parse_date":
            {
                var r = $"(s.parse_date {a[0]} {a[1]})";
                return Fact(r, $"(=> {IsSome(TType.Date, r, tx)} (and (<= 0 {ValueOf(r)}) (<= {ValueOf(r)} {MaxDay})))");
            }
            case "parse_time":
            {
                var r = $"(s.parse_time {a[0]} {a[1]})";
                return Fact(r, $"(=> {IsSome(TType.Int, r, tx)} (and (<= 0 {ValueOf(r)}) (<= {ValueOf(r)} 1439)))");
            }
            case "to_decimal": return $"(to_real {a[0]})";
            case "dec_round":
            {
                Oblige(tx, $"(and (<= 0 {a[1]}) (<= {a[1]} 28))", "TN3007", $"rounding position might be out of range: {Text(c)}", c.Span,
                    "Decimals round to between 0 and 28 decimal places.");
                if (!long.TryParse(a[1], out var places) || places > 28) return $"(d.round {a[0]} {a[1]})";
                var f = $"{BigInteger.Pow(10, (int)places)}.0";
                return $"(ite (>= {a[0]} 0.0) (/ (to_real (to_int (+ (* {a[0]} {f}) 0.5))) {f}) (- (/ (to_real (to_int (+ (* (- {a[0]}) {f}) 0.5))) {f})))";
            }
            case "to_int":
            {
                if (ArgT(0).Kind != TK.Decimal) return a[0];
                var r = $"(ite (>= {a[0]} 0.0) (to_int {a[0]}) (- (to_int (- {a[0]}))))";
                Oblige(tx, InRange(r), "TN3013", $"conversion to Int might fail: {Text(c)}", c.Span, "Prove the integer part of the decimal fits in 64 bits.");
                return r;
            }
            case "to_int32":
                Oblige(tx, InRange32(a[0]), "TN3013", $"conversion to Int32 might fail: {Text(c)}", c.Span, "Prove the value is between -2147483648 and 2147483647.");
                return a[0];
            case "has_bit":
                Oblige(tx, $"(and (<= 0 {a[1]}) (< {a[1]} 63))", "TN3007", $"bit position might be out of range: {Text(c)}", c.Span, "Prove 0 <= bit < 63.");
                return $"(= (mod (div {a[0]} {Pow2(a[1])}) 2) 1)";
            case "date":
                Oblige(tx, $"(d.valid {a[0]} {a[1]} {a[2]})", "TN3015", $"date might be invalid: {Text(c)}", c.Span,
                    "Prove 1 <= year <= 9999, 1 <= month <= 12 and 1 <= day <= the number of days in that month, or test is_valid_date first.");
                return $"(d.from {a[0]} {a[1]} {a[2]})";
            case "is_valid_date": return $"(d.valid {a[0]} {a[1]} {a[2]})";
            case "add_days":
            {
                var r = $"(+ {a[0]} {a[1]})";
                Oblige(tx, $"(and (<= 0 {r}) (<= {r} {MaxDay}))", "TN3015", $"date might be out of range: {Text(c)}", c.Span,
                    "Dates run from 0001-01-01 to 9999-12-31. Bound the number of days added.");
                return r;
            }
            case "days_between": return $"(- {a[1]} {a[0]})";
            case "day_of_week": return $"(mod (+ {a[0]} 1) 7)";
            case "year" or "month" or "day":
            {
                // True of every valid day number, but out of the solver's reach through the calendar arithmetic.
                var r = $"(d.{c.Name} {a[0]})";
                AddFact(tx, $"(<= 1 {r} {c.Name switch { "year" => 9999, "month" => 12, _ => 31 }})");
                return r;
            }
            case "append": return $"(mk (store (elems {a[0]}) (alen {a[0]}) {a[1]}) (+ (alen {a[0]}) 1))";
            case "concat":
            {
                var r = FreshIn(tx, c.Type, "concat");
                var i = $"i!{_fresh++}";
                Fact(r, $"(= (alen {r}) (+ (alen {a[0]}) (alen {a[1]})))");
                Fact(r, $"(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} (alen {a[0]}))) (= (select (elems {r}) {i}) (select (elems {a[0]}) {i}))))");
                return Fact(r, $"(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} (alen {a[1]}))) (= (select (elems {r}) (+ (alen {a[0]}) {i})) (select (elems {a[1]}) {i}))))");
            }
            case "map_empty" or "set_empty":
            {
                var key = c.Type.Kind == TK.Map ? c.Type.Key : c.Type.Elem!;
                var dflt = $"dflt!{_fresh++}";
                Declare($"(declare-const {dflt} {Sort(key, tx)})");
                var keys = $"(mk ((as const (Array Int {Sort(key, tx)})) {dflt}) 0)";
                return c.Type.Kind == TK.Map
                    ? $"(mkm ((as const (Array {Sort(key, tx)} {Sort(OptionOf(c.Type.Value), tx)})) {NoneOf(c.Type.Value, tx)}) 0 {keys})"
                    : $"(mks ((as const (Array {Sort(key, tx)} Bool)) false) 0 {keys})";
            }
            case "map_put":
            {
                var (m, k, v) = (a[0], a[1], a[2]);
                var has = IsSome(ArgT(0).Value, $"(select (mget {m}) {k})", tx);
                var keys = $"(mkeys {m})";
                return $"(mkm (store (mget {m}) {k} {SomeOf(ArgT(0).Value, v, tx)}) (ite {has} (msize {m}) (+ (msize {m}) 1)) " +
                       $"(ite {has} {keys} (mk (store (elems {keys}) (alen {keys}) {k}) (+ (alen {keys}) 1))))";
            }
            case "map_get": return $"(select (mget {a[0]}) {a[1]})";
            case "map_has": return IsSome(ArgT(0).Value, $"(select (mget {a[0]}) {a[1]})", tx);
            case "map_get_or":
            {
                var o = $"(select (mget {a[0]}) {a[1]})";
                return $"(ite {IsSome(ArgT(0).Value, o, tx)} {ValueOf(o)} {a[2]})";
            }
            case "map_remove":
            {
                var (m, k) = (a[0], a[1]);
                var has = IsSome(ArgT(0).Value, $"(select (mget {m}) {k})", tx);
                var size = $"(ite {has} (- (msize {m}) 1) (msize {m}))";
                var keys = FreshIn(tx, TType.ArrayOf(ArgT(0).Key), "keys");
                var i = $"i!{_fresh++}";
                Fact(keys, $"(= (alen {keys}) {size})");
                Fact(keys, $"(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} (alen {keys}))) (not (= (select (elems {keys}) {i}) {k}))))");
                return $"(mkm (store (mget {m}) {k} {NoneOf(ArgT(0).Value, tx)}) {size} {keys})";
            }
            case "map_size": return $"(msize {a[0]})";
            case "map_keys": return $"(mkeys {a[0]})";
            case "map_values":
            {
                var m = a[0];
                var r = FreshIn(tx, c.Type, "values");
                var i = $"i!{_fresh++}";
                Fact(r, $"(= (alen {r}) (msize {m}))");
                return Fact(r, $"(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} (msize {m}))) (= (select (mget {m}) (select (elems (mkeys {m})) {i})) {SomeOf(ArgT(0).Value, $"(select (elems {r}) {i})", tx)})))");
            }
            case "set_of":
            {
                var arr = a[0];
                var r = FreshIn(tx, c.Type, "set");
                var elem = ArgT(0).Elem!;
                var (i, x) = ($"i!{_fresh++}", $"x!{_fresh++}");
                var w = FreshFn(tx, [Sort(elem, tx)], "Int", "set.w");
                var n = $"(alen {arr})";
                Fact(r, $"(forall (({i} Int)) (=> (and (<= 0 {i}) (< {i} {n})) (select (smem {r}) (select (elems {arr}) {i}))))");
                Fact(r, $"(forall (({x} {Sort(elem, tx)})) {Triggered($"(=> (select (smem {r}) {x}) (and (<= 0 {w([x])}) (< {w([x])} {n}) (= (select (elems {arr}) {w([x])}) {x})))", $"(select (smem {r}) {x})")})");
                Fact(r, $"(and (<= (ssize {r}) {n}) (= (> {n} 0) (> (ssize {r}) 0)))");
                return Fact(r, TypeFact(c.Type, r)!);
            }
            case "set_add":
            {
                var (s, x) = (a[0], a[1]);
                var has = $"(select (smem {s}) {x})";
                var items = $"(sitems {s})";
                return $"(mks (store (smem {s}) {x} true) (ite {has} (ssize {s}) (+ (ssize {s}) 1)) " +
                       $"(ite {has} {items} (mk (store (elems {items}) (alen {items}) {x}) (+ (alen {items}) 1))))";
            }
            case "set_has": return $"(select (smem {a[0]}) {a[1]})";
            case "set_size": return $"(ssize {a[0]})";
            case "set_items": return $"(sitems {a[0]})";
            case "is_some": return IsSome(ArgT(0).Args[0], a[0], tx);
            case "is_none": return Not(IsSome(ArgT(0).Args[0], a[0], tx));
            case "unwrap_or": return $"(ite {IsSome(ArgT(0).Args[0], a[0], tx)} {ValueOf(a[0])} {a[1]})";
            default: return null;
        }
    }

    /// <summary>
    /// Translates a lambda's body with its parameters bound to <paramref name="terms"/>, inside 'forall binder' guarded
    /// by <paramref name="guard"/>: obligations in the body must hold for every element, and contract facts are closed
    /// over the binder.
    /// </summary>
    private string Apply(Tx tx, Lambda lam, string binder, string guard, params string[] terms)
    {
        tx.Ctx.Add((true, $"({binder} Int)"));
        tx.Ctx.Add((false, guard));
        for (var k = 0; k < terms.Length; k++) tx.Bound[lam.Params[k]] = terms[k];
        var r = T(lam.Body, tx);
        foreach (var p in lam.Params) tx.Bound.Remove(p);
        tx.Ctx.RemoveRange(tx.Ctx.Count - 2, 2);
        return r;
    }

    /// <summary>
    /// Collection builtins that take a lambda. Each is described exactly where that is cheap (map, any, all, count,
    /// fold, sum_by, filter and find through prefix functions) and by its key properties otherwise (sort_by: sorted
    /// permutation; group_by and to_map: every key present).
    /// </summary>
    private string TLambdaBuiltin(Call c, Tx tx)
    {
        var a = T(c.Args[0], tx);
        var elemT = c.Args[0].Type.Elem!;
        var n = $"(alen {a})";
        string E(string idx) => $"(select (elems {a}) {idx})";
        var i = $"i!{_fresh++}";
        var range = $"(and (<= 0 {i}) (< {i} {n}))";
        var facts = new List<string>();
        if (TypeFact(elemT, E(i)) is { } ef) facts.Add($"(forall (({i} Int)) (=> {range} {ef}))");
        string Done(string term)
        {
            if (tx.Instantiate) foreach (var f in facts) AddFact(tx, f);
            return term;
        }
        var lam = (Lambda)c.Args[c.Name is "fold" or "to_map" ? 2 : 1];
        string Forall(string body, string? pattern = null) =>
            pattern == null ? $"(forall (({i} Int)) (=> {range} {body}))" : $"(forall (({i} Int)) {Triggered($"(=> {range} {body})", pattern)})";
        string Exists(string body) => $"(exists (({i} Int)) (and {range} {body}))";

        // A prefix function f(k) over the first k elements: f(0) = start and f(k) = step(f(k - 1), element k - 1). It is
        // stated backwards and triggered on f(k), so a term f(n) unfolds down to f(0) for a concrete n and stops there.
        Func<string[], string> Prefix(string sort, string hint, string start, Func<string, string, string> step)
        {
            var f = FreshFn(tx, ["Int"], sort, hint);
            var k = $"k!{_fresh++}";
            var prev = f([$"(- {k} 1)"]);
            facts.Add($"(= {f(["0"])} {start})");
            facts.Add($"(forall (({k} Int)) {Triggered($"(=> (and (< 0 {k}) (<= {k} {n})) (= {f([k])} {step(prev, $"(- {k} 1)")}))", f([k]))})");
            return f;
        }
        // c(k): how many of the first k elements satisfy the predicate p (translated at element i).
        Func<string[], string> Counter(string p) => Prefix("Int", "cnt", "0", (prev, at) => $"(+ {prev} (ite {At(p, at)} 1 0))");
        // The element-i term p, read at another index.
        string At(string p, string idx) => Replace(p, i, idx);
        string Le(TType k, string x, string y) => k.Kind == TK.String ? $"(str.<= {x} {y})" : $"(<= {x} {y})";
        string Lt(TType k, string x, string y) => k.Kind == TK.String ? $"(str.< {x} {y})" : $"(< {x} {y})";

        switch (c.Name)
        {
            case "map":
            {
                var p = Apply(tx, lam, i, range, E(i));
                var r = FreshIn(tx, c.Type, "map");
                facts.Add($"(= (alen {r}) {n})");
                facts.Add(Forall($"(= (select (elems {r}) {i}) {p})", $"(select (elems {r}) {i})"));
                return Done(r);
            }
            case "any": return Done(Exists(Apply(tx, lam, i, range, E(i))));
            case "all": return Done(Forall(Apply(tx, lam, i, range, E(i))));
            case "count":
            {
                var p = Apply(tx, lam, i, range, E(i));
                var r = Counter(p)([n]);
                facts.Add($"(and (<= 0 {r}) (<= {r} {n}) (= (= {r} {n}) {Forall(p)}) (= (= {r} 0) (not {Exists(p)})))");
                return Done(r);
            }
            case "filter":
            {
                var p = Apply(tx, lam, i, range, E(i));
                var r = FreshIn(tx, c.Type, "filter");
                var cnt = Counter(p);
                var w = FreshFn(tx, ["Int"], "Int", "filter.w");
                facts.Add(Forall($"(=> {p} (and (= {w([cnt([i])])} {i}) (= (select (elems {r}) {cnt([i])}) {E(i)})))"));
                facts.Add($"(and (= (alen {r}) {cnt([n])}) (<= 0 (alen {r})) (<= (alen {r}) {n}))");
                var j = $"j!{_fresh++}";
                var rangeR = $"(and (<= 0 {j}) (< {j} (alen {r})))";
                var pr = Apply(NoChecks(tx), lam, j, rangeR, $"(select (elems {r}) {j})");
                facts.Add($"(forall (({j} Int)) {Triggered($"(=> {rangeR} (and {pr} (<= 0 {w([j])}) (< {w([j])} {n}) (= (select (elems {r}) {j}) {E(w([j]))})))", $"(select (elems {r}) {j})")})");
                return Done(r);
            }
            case "find" or "find_last":
            {
                var p = Apply(tx, lam, i, range, E(i));
                var any = Exists(p);
                var w = FreshIn(tx, TType.Int, "found");
                facts.Add($"(=> {any} (and (<= 0 {w}) (< {w} {n})))");
                facts.Add(Forall($"(=> (and {any} (= {i} {w})) {p})"));
                facts.Add(Forall($"(=> (and {any} ({(c.Name == "find" ? "<" : ">")} {i} {w})) (not {p}))"));
                return Done($"(ite {any} {SomeOf(elemT, E(w), tx)} {NoneOf(elemT, tx)})");
            }
            case "sum_by":
            {
                var p = Apply(tx, lam, i, range, E(i));
                var zero = c.Type.Kind == TK.Decimal ? "0.0" : "0";
                var sm = Prefix(Sort(c.Type, tx), "sum", zero, (prev, at) => $"(+ {prev} {At(p, at)})");
                facts.Add($"(=> {Forall($"(>= {p} {zero})")} (>= {sm([n])} {zero}))");
                if (tx.Exec && _cur.Total && c.Type.Kind is TK.Int or TK.Int32)
                {
                    if (tx.Instantiate) foreach (var f in facts) AddFact(tx, f);
                    facts.Clear();
                    var k = $"k!{_fresh++}";
                    var inRange = c.Type.Kind == TK.Int32 ? InRange32(sm([k])) : InRange(sm([k]));
                    Oblige(tx, $"(forall (({k} Int)) (=> (and (<= 0 {k}) (<= {k} {n})) {inRange}))", "TN3011", $"integer overflow possible: {Text(c)}", c.Span,
                        "In a 'total' function every partial sum must stay in range. Bound the elements and the length of the array.");
                }
                return Done(sm([n]));
            }
            case "min_by" or "max_by":
            {
                var keyT = lam.Type;
                var kp = Apply(tx, lam, i, range, E(i));
                var w = FreshIn(tx, TType.Int, "best");
                var kw = FreshIn(tx, keyT, "bestkey");
                var min = c.Name == "min_by";
                facts.Add($"(=> (> {n} 0) (and (<= 0 {w}) (< {w} {n})))");
                facts.Add(Forall($"(=> (= {i} {w}) (= {kp} {kw}))"));
                facts.Add(Forall(min ? Le(keyT, kw, kp) : Le(keyT, kp, kw)));
                facts.Add(Forall($"(=> (< {i} {w}) {(min ? Lt(keyT, kw, kp) : Lt(keyT, kp, kw))})"));
                return Done($"(ite (> {n} 0) {SomeOf(elemT, E(w), tx)} {NoneOf(elemT, tx)})");
            }
            case "sort_by" or "sort_by_desc":
            {
                var keyT = lam.Type;
                Apply(tx, lam, i, range, E(i));
                var r = FreshIn(tx, c.Type, "sorted");
                var p = FreshFn(tx, ["Int"], "Int", "perm");
                var q = FreshFn(tx, ["Int"], "Int", "inv");
                var j = $"j!{_fresh++}";
                var rangeR = $"(and (<= 0 {j}) (< {j} {n}))";
                facts.Add($"(= (alen {r}) {n})");
                facts.Add($"(forall (({j} Int)) (=> {rangeR} (and (<= 0 {p([j])}) (< {p([j])} {n}) (= (select (elems {r}) {j}) {E(p([j]))}) (= {q([p([j])])} {j}))))");
                facts.Add(Forall($"(and (<= 0 {q([i])}) (< {q([i])} {n}) (= {p([q([i])])} {i}))"));
                var adjacent = $"(and (<= 0 {j}) (< (+ {j} 1) {n}))";
                var k1 = Apply(NoChecks(tx), lam, j, adjacent, $"(select (elems {r}) {j})");
                var k2 = Apply(NoChecks(tx), lam, j, adjacent, $"(select (elems {r}) (+ {j} 1))");
                facts.Add($"(forall (({j} Int)) (=> {adjacent} {(c.Name == "sort_by" ? Le(keyT, k1, k2) : Le(keyT, k2, k1))}))");
                return Done(r);
            }
            case "group_by" or "to_map":
            {
                var keyLam = (Lambda)c.Args[1];
                var kp = Apply(tx, keyLam, i, range, E(i));
                if (c.Name == "to_map") Apply(tx, lam, i, range, E(i));
                var r = FreshIn(tx, c.Type, c.Name);
                facts.Add(TypeFact(c.Type, r)!);
                facts.Add(Forall(IsSome(c.Type.Value, $"(select (mget {r}) {kp})", tx)));
                facts.Add($"(and (<= (msize {r}) {n}) (= (> {n} 0) (> (msize {r}) 0)))");
                return Done(r);
            }
            case "fold":
            {
                var init = T(c.Args[1], tx);
                // The accumulator is a placeholder symbol while the body is translated, then replaced by f(k - 1).
                var acc = $"acc!{_fresh++}";
                Declare($"(declare-const {acc} {Sort(c.Type, tx)})");
                var body = Apply(tx, lam, i, range, acc, E(i));
                var fo = Prefix(Sort(c.Type, tx), "fold", init, (prev, at) => Replace(At(body, at), acc, prev));
                return Done(fo([n]));
            }
            default:
                throw new InvalidOperationException(c.Name);
        }
    }

    /// <summary>Facts about tensor elements in the real-number model, for value-range contracts.</summary>
    private void ElemAxioms(Call c, string r, List<string> a, Tx tx)
    {
        if (!tx.Instantiate) return;
        var i = $"i!{_fresh++}";
        string El(string t) => $"(el {t} {i})";
        var body = c.Name switch
        {
            "relu" => $"(= {El(r)} (ite (>= {El(a[0])} 0.0) {El(a[0])} 0.0))",
            "add" => $"(= {El(r)} (+ {El(a[0])} {El(a[1])}))",
            "sub" => $"(= {El(r)} (- {El(a[0])} {El(a[1])}))",
            "mul" => $"(= {El(r)} (* {El(a[0])} {El(a[1])}))",
            "scale" => $"(= {El(r)} (* {El(a[0])} (fp.to_real {a[1]})))",
            "sigmoid" or "softmax" => $"(and (<= 0.0 {El(r)}) (<= {El(r)} 1.0))",
            "tanh" => $"(and (<= (- 1.0) {El(r)}) (<= {El(r)} 1.0))",
            "reshape" or "to_f32" or "to_f64" => $"(= {El(r)} {El(a[0])})",
            "full" => $"(= {El(r)} (fp.to_real {a[0]}))",
            "add_bias" => $"(= {El(r)} (+ {El(a[0])} (el {a[1]} (mod {i} {DimT(c.Type.Dims[1], tx)}))))",
            _ => null,
        };
        if (body == null) return;
        AddFact(tx, $"(forall (({i} Int)) (! (=> (and (<= 0 {i}) (< {i} {SizeTerm(c.Type, tx)})) {body}) :pattern ((el {r} {i}))))");
        if (c.Name == "softmax")
        {
            var k = $"k!{_fresh++}";
            AddFact(tx, $"(forall (({k} Int)) (! (=> (and (<= 0 {k}) (< {k} {DimT(c.Type.Dims[0], tx)})) (= (row_sum {r} {k}) 1.0)) :pattern ((row_sum {r} {k}))))");
        }
    }

    private string DimT(Dim d, Tx tx) =>
        d.Lit is { } v ? v.ToString()
        : d.Name != null ? tx.Env[d.Name].Term
        : $"({d.Op} {DimT(d.L!, tx)} {DimT(d.R!, tx)})";

    private string SizeTerm(TType t, Tx tx) => t.Dims.Count == 0 ? "1" : t.Dims.Count == 1 ? DimT(t.Dims[0], tx) : $"(* {string.Join(" ", t.Dims.Select(d => DimT(d, tx)))})";

    private static string Guarded(Tx tx, string guard, Func<string> inner)
    {
        tx.Ctx.Add((false, guard));
        var r = inner();
        tx.Ctx.RemoveAt(tx.Ctx.Count - 1);
        return r;
    }

    /// <summary>Records a fact that holds unconditionally (such as an instantiated contract), closed over enclosing binders.</summary>
    private static void AddFact(Tx tx, string fact)
    {
        foreach (var (binder, text) in Enumerable.Reverse(tx.Ctx))
            if (binder) fact = $"(forall ({text}) {fact})";
        tx.S.Path.Add(fact);
    }

    private void Oblige(Tx tx, string cond, string code, string message, Span span, string hint)
    {
        if (!tx.Checks) return;
        foreach (var (binder, text) in Enumerable.Reverse(tx.Ctx))
            cond = binder ? $"(forall ({text}) {cond})" : $"(=> {text} {cond})";
        Prove(tx.S, cond, code, message, span, hint);
        // Assert, then assume: later queries reuse the fact instead of re-deriving it. If it was not proved, the
        // module is already rejected, so assuming it cannot let a wrong program through.
        tx.S.Path.Add(cond);
    }

    // ---------- solver ----------

    private void Prove(State s, string goal, string code, string message, Span span, string hint)
    {
        var (verdict, model) = Query(s, goal, code);
        if (verdict == Verdict.Proved) return;
        var holes = _holes.Where(h => goal.Contains(h.Sym)).ToList();
        if (holes.Count > 0)
        {
            foreach (var h in holes) h.Obligations.Add(message);
            return;
        }
        var refuted = verdict == Verdict.Refuted;
        diags.Add("error", code, span, refuted ? message : $"{message} (the solver could not decide within {timeoutMs} ms)", hint,
            refuted ? "refuted" : "unknown", refuted && model!.Count > 0 ? model : null);
    }

    private (Verdict Verdict, Dictionary<string, string>? Model) Query(State s, string goal, string label)
    {
        var sb = new StringBuilder(Prelude).Append(LibraryPrelude).Append(_typeDecls).Append(TypedPrelude).Append(_fnDecls);
        foreach (var d in _decls) sb.AppendLine(d);
        foreach (var fact in s.Path) sb.AppendLine($"(assert {fact})");
        sb.AppendLine($"(assert (not {goal}))");
        // Observers: constants pinned to the current value of each variable, so a model reads back as a counterexample.
        var observed = new List<(string Name, TType Type)>();
        foreach (var (name, (term, type)) in s.Store)
        {
            if (!Regex.IsMatch(name, @"^[A-Za-z_][A-Za-z0-9_]*$")) continue;
            switch (type.Kind)
            {
                case TK.Int or TK.Bool or TK.Float or TK.Named or TK.Int32 or TK.String or TK.Date or TK.Decimal:
                    sb.AppendLine($"(declare-const cex.{name} {Sort(type)}) (assert (= cex.{name} {term}))");
                    observed.Add((name, type));
                    break;
                case TK.Map or TK.Set:
                    sb.AppendLine($"(declare-const cex.{name}.len Int) (assert (= cex.{name}.len ({(type.Kind == TK.Map ? "msize" : "ssize")} {term})))");
                    observed.Add((name, type));
                    break;
                case TK.Array when type.Elem!.Kind is TK.Int or TK.Bool or TK.Float or TK.Int32 or TK.String or TK.Date or TK.Decimal:
                    sb.AppendLine($"(declare-const cex.{name}.len Int) (assert (= cex.{name}.len (alen {term})))");
                    for (var k = 0; k < ArrayPreview; k++)
                        sb.AppendLine($"(declare-const cex.{name}.{k} {Sort(type.Elem!)}) (assert (= cex.{name}.{k} (select (elems {term}) {k})))");
                    observed.Add((name, type));
                    break;
            }
        }
        var text = sb.ToString();
        var id = ++_queries;
        smtSink?.Invoke($"{_cur.Name}-{id:000}-{label}", text + "(check-sat)\n");

        var solver = _z3.MkSolver();
        var ps = _z3.MkParams();
        ps.Add("timeout", (uint)timeoutMs);
        solver.Parameters = ps;
        solver.Assert(_z3.ParseSMTLIB2String(text));
        var status = solver.Check();
        if (status == Status.UNSATISFIABLE) return (Verdict.Proved, null);
        if (status == Status.UNKNOWN) return (Verdict.Unknown, null);

        var raw = new Dictionary<string, string>();
        foreach (var d in solver.Model.ConstDecls)
        {
            var name = d.Name.ToString();
            if (name.StartsWith("cex.")) raw[name[4..]] = ShowValue(solver.Model.ConstInterp(d));
        }
        var model = new Dictionary<string, string>();
        foreach (var (name, type) in observed)
        {
            if (type.Kind is TK.Map or TK.Set)
            {
                if (raw.TryGetValue($"{name}.len", out var size)) model[name] = $"{(type.Kind == TK.Map ? "map" : "set")} of size {size}";
                continue;
            }
            if (type.Kind != TK.Array) { if (raw.TryGetValue(name, out var v)) model[name] = Display(v, type); continue; }
            if (!raw.TryGetValue($"{name}.len", out var lenText) || !long.TryParse(lenText, out var len)) continue;
            var shown = Enumerable.Range(0, (int)Math.Clamp(len, 0, ArrayPreview)).Select(k => raw.TryGetValue($"{name}.{k}", out var ev) ? Display(ev, type.Elem!) : "?");
            model[name] = $"[{string.Join(", ", shown)}{(len > ArrayPreview ? ", ..." : "")}] (len {len})";
        }
        return (Verdict.Refuted, model);
    }

    /// <summary>Model values in source notation: dates as yyyy-MM-dd, decimals with an 'm' suffix.</summary>
    private static string Display(string v, TType t)
    {
        switch (t.Kind)
        {
            case TK.Date when long.TryParse(v, out var day) && day is >= 0 and <= MaxDay:
                return DateOnly.FromDayNumber((int)day).ToString("yyyy-MM-dd", System.Globalization.CultureInfo.InvariantCulture);
            case TK.Decimal:
            {
                var m = Regex.Match(v, @"^(-?)(\d+)(?:/(\d+))?$");
                if (!m.Success) return v;
                var num = BigInteger.Parse(m.Groups[2].Value);
                var den = m.Groups[3].Success ? BigInteger.Parse(m.Groups[3].Value) : BigInteger.One;
                var whole = BigInteger.DivRem(num, den, out var rest);
                var digits = new StringBuilder();
                for (var k = 0; k < 28 && !rest.IsZero; k++)
                {
                    rest *= 10;
                    digits.Append(BigInteger.DivRem(rest, den, out rest));
                }
                return $"{m.Groups[1].Value}{whole}{(digits.Length > 0 ? "." + digits : "")}{(rest.IsZero ? "" : "...")}m";
            }
            default: return v;
        }
    }

    private static string ShowValue(Microsoft.Z3.Expr v)
    {
        if (v is RatNum rat)
        {
            var (num, den) = (rat.BigIntNumerator, rat.BigIntDenominator);
            return den.IsOne ? num.ToString() : $"{num}/{den}";
        }
        if (v is FPNum fp)
        {
            if (fp.IsNaN) return "NaN";
            if (fp.IsInf) return fp.Sign ? "-inf" : "inf";
            var bits = ((fp.Sign ? 1UL : 0UL) << 63) | ((ulong)fp.ExponentInt64(true) << 52) | fp.SignificandUInt64;
            return BitConverter.Int64BitsToDouble((long)bits).ToString("R", System.Globalization.CultureInfo.InvariantCulture);
        }
        var s = v.ToString();
        s = Regex.Replace(s, @"\(- (\d+)\)", "-$1");
        s = Regex.Replace(s, @"\(as c\.(\w+) [^)]*\)+", "$1");
        return Regex.Replace(s, @"\bc\.", "");
    }

    // ---------- helpers ----------

    private static void Bind(State s, string name, string term, TType type) => s.Store[name] = (term, type);

    private string Fresh(TType type, string hint)
    {
        var sym = $"{hint}!{_fresh++}";
        Declare($"(declare-const {sym} {Sort(type)})");
        return sym;
    }

    private static string InBounds(string array, string index) => $"(and (<= 0 {index}) (< {index} (alen {array})))";

    private static string Not(string t) => t switch { "true" => "false", "false" => "true", _ => $"(not {t})" };

    // Z3 rejects patterns that contain 'ite' or connectives, including through the prelude's macros, which it expands;
    // quantifiers over such terms go without one.
    private static readonly Regex Unpatternable = new(@"\((ite|or|and|not|=>|=|s\.int|d\.[a-z]+|tdiv|tmod) ");

    private static string Triggered(string body, string trigger) =>
        Unpatternable.IsMatch(trigger) ? body : $"(! {body} :pattern ({trigger}))";

    private static string And(List<string> terms) => terms.Count switch
    {
        0 => "true",
        1 => terms[0],
        _ => $"(and {string.Join(" ", terms)})",
    };

    private static string Or(List<string> terms) => terms.Count switch
    {
        0 => "false",
        1 => terms[0],
        _ => $"(or {string.Join(" ", terms)})",
    };

    /// <summary>The exact IEEE double, as its bit pattern.</summary>
    private static string FpLit(double v)
    {
        if (double.IsNaN(v)) return "(_ NaN 11 53)";
        var bits = BitConverter.DoubleToInt64Bits(v);
        var exp = Convert.ToString((bits >> 52) & 0x7FF, 2).PadLeft(11, '0');
        var mant = Convert.ToString(bits & ((1L << 52) - 1), 2).PadLeft(52, '0');
        return $"(fp #b{(bits < 0 ? 1 : 0)} #b{exp} #b{mant})";
    }

    /// <summary>The exact rational value of a finite double.</summary>
    private static string RealLit(double v)
    {
        if (v == 0) return "0.0";
        var bits = BitConverter.DoubleToInt64Bits(v);
        var exp = (int)((bits >> 52) & 0x7FF);
        var mant = bits & ((1L << 52) - 1);
        if (exp == 0) exp = 1; else mant |= 1L << 52;
        exp -= 1075;
        BigInteger num = mant, den = 1;
        if (exp > 0) num <<= exp; else den <<= -exp;
        var g = BigInteger.GreatestCommonDivisor(num, den);
        (num, den) = (num / g, den / g);
        var r = den.IsOne ? $"{num}.0" : $"(/ {num}.0 {den}.0)";
        return v < 0 ? $"(- {r})" : r;
    }

    private string Text(Expr e)
    {
        if (e.Span.File < 0 || e.Span.File >= sources.Count) return "<generated>";
        var source = sources[e.Span.File];
        return e.Span.End <= source.Length && e.Span.Start < e.Span.End ? source[e.Span.Start..e.Span.End] : "<generated>";
    }
}
