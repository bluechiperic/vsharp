namespace VSharp.Compiler;

/// <summary>
/// Reverse-mode differentiation as a source transformation. 'fn d = grad f wrt p' becomes an ordinary V# function
/// with f's parameters that returns the gradient of f with respect to p. The generated body is checked and verified like
/// any other function. f must be straight-line code (let, assert, return) over Float and tensor operations; calls to other
/// straight-line functions are inlined.
/// </summary>
public sealed class Grad(DiagnosticBag diags)
{
    private sealed record Node(string Name, Expr Rhs, TType Type, bool Dep);

    private sealed class Ctx
    {
        public Dictionary<string, (Expr Atom, bool Dep)> Env { get; } = [];
        public Dictionary<string, Dim> Dims { get; init; } = [];
    }

    private readonly List<Node> _nodes = [];
    private readonly Dictionary<string, TType> _types = [];
    private readonly HashSet<string> _dep = [];
    private int _n;
    private Span _at;
    private bool _failed;

    public static bool Signature(FnDecl g, FnDecl? of, DiagnosticBag diags)
    {
        g.Ret = TType.Error;
        if (of == null || of.Kind != FnKind.Fn)
        {
            diags.Error("TN2015", g.NameSpan, of == null ? $"unknown function '{g.GradOf}'" : $"'{of.Name}' is not an ordinary function and cannot be differentiated");
            return false;
        }
        var p = of.Params.FirstOrDefault(x => x.Name == g.GradWrt);
        if (p == null)
        {
            diags.Error("TN2015", g.NameSpan, $"'{of.Name}' has no parameter '{g.GradWrt}'");
            return false;
        }
        if (of.Ret.Kind != TK.Float || p.Type.Kind is not (TK.Float or TK.Tensor) || of.TypeParams.Count > 0)
        {
            diags.Error("TN2015", g.NameSpan, $"'grad' needs a non-generic function returning Float, differentiated with respect to a Float or tensor parameter",
                $"'{of.Name}' returns {of.Ret} and '{p.Name}' has type {p.Type}.");
            return false;
        }
        g.DimParams.AddRange(of.DimParams);
        foreach (var q in of.Params) g.Params.Add(new Param(q.Name, q.Type, q.Span));
        g.Ret = p.Type.Base;
        g.Effects.UnionWith(of.Effects);
        g.Total = of.Total;
        return true;
    }

    public bool Body(FnDecl g, FnDecl of)
    {
        _at = g.NameSpan;
        var ctx = new Ctx();
        foreach (var p in of.Params)
        {
            var dep = p.Name == g.GradWrt;
            ctx.Env[p.Name] = (V(p.Name), dep);
            _types[p.Name] = p.Type.Base;
            if (dep) _dep.Add(p.Name);
        }
        foreach (var d in of.DimParams) ctx.Dims[d] = Dim.Var(d);
        var result = Inline(of, ctx);
        if (_failed || result == null) return false;

        var body = _nodes.Select(n => (Stmt)new Let(n.Name, false, null, n.Rhs) { Span = _at }).ToList();
        var contrib = new Dictionary<string, List<Expr>>();
        void Add(Expr atom, Expr c)
        {
            if (atom is Var v && _dep.Contains(v.Name)) (contrib.TryGetValue(v.Name, out var l) ? l : contrib[v.Name] = []).Add(c);
        }
        Add(result, F(1.0));
        for (var i = _nodes.Count - 1; i >= 0; i--)
        {
            var node = _nodes[i];
            if (!node.Dep || !contrib.TryGetValue(node.Name, out var cs)) continue;
            var dname = $"$d{node.Name[1..]}";
            body.Add(new Let(dname, false, null, Sum(cs, node.Type)) { Span = _at });
            _types[dname] = node.Type;
            Backward(node, V(dname), Add);
            if (_failed) return false;
        }
        var wrt = g.GradWrt!;
        var grad = contrib.TryGetValue(wrt, out var wc) ? Sum(wc, _types[wrt]) : Zero(_types[wrt]);
        body.Add(new Return(grad) { Span = _at });

        g.Body = body;
        foreach (var r in of.Requires) g.Requires.Add(Rewrite(r, _ => null, new Dictionary<string, Dim>()));
        g.EndSpan = _at;
        return true;
    }

    // ---------- forward: lowering to one operation per 'let' ----------

    private Expr? Inline(FnDecl f, Ctx ctx)
    {
        foreach (var s in f.Body)
        {
            switch (s)
            {
                case Let { Mutable: false, Ghost: false } l:
                    var atom = Lower(l.Init, ctx);
                    if (atom == null) return null;
                    ctx.Env[l.Name] = (atom, IsDep(atom));
                    break;
                case Assert or Let { Ghost: true }:
                    break;
                case Return r:
                    return Lower(r.Value, ctx);
                default:
                    return Fail($"'{f.Name}' is not straight-line code: only 'let', 'assert' and 'return' can be differentiated");
            }
        }
        return Fail($"'{f.Name}' does not end in 'return'");
    }

    private Expr? Lower(Expr e, Ctx ctx)
    {
        if (e.Type.Kind is not (TK.Float or TK.Tensor)) return Const(e, ctx);
        switch (e)
        {
            case FloatLit or TensorLit: return Const(e, ctx);
            case Var v when v.Kind is VarKind.Local or VarKind.Param: return Copy(ctx.Env[v.Name].Atom);
            case Unary u:
            {
                var a = Lower(u.Operand, ctx);
                return a == null ? null : Emit(new Unary("-", a), e, ctx);
            }
            case Binary b:
            {
                var (l, r) = (Lower(b.Left, ctx), Lower(b.Right, ctx));
                return l == null || r == null ? null : Emit(new Binary(b.Op, l, r), e, ctx);
            }
            case Call { IsBuiltin: true } c:
            {
                var args = new List<Expr>();
                foreach (var a in c.Args)
                {
                    var x = Lower(a, ctx);
                    if (x == null) return null;
                    args.Add(x);
                }
                if (!args.Any(IsDep)) return Const(e, ctx);
                return Emit(new Call(c.Name, args, args.Select(_ => (string?)null).ToList()) { ShapeArg = c.ShapeArg?.Subst(new Dictionary<string, TType>(), ctx.Dims) }, e, ctx);
            }
            case Call { Target: { Kind: FnKind.Fn } f } c when f.IsPure:
            {
                var inner = new Ctx { Dims = f.DimParams.ToDictionary(d => d, d => c.DimArgs[d].Subst(ctx.Dims)) };
                for (var i = 0; i < c.Args.Count; i++)
                {
                    var x = Lower(c.Args[i], ctx);
                    if (x == null) return null;
                    inner.Env[f.Params[i].Name] = (x, IsDep(x));
                }
                return Inline(f, inner);
            }
            default:
                return Fail($"cannot differentiate through this expression ({e.GetType().Name})",
                    "Differentiable code uses Float arithmetic, tensor builtins and calls to other straight-line functions.");
        }
    }

    private Expr Const(Expr e, Ctx ctx) => Rewrite(e, n => ctx.Env.TryGetValue(n, out var a) ? Copy(a.Atom) : null, ctx.Dims);

    private bool IsDep(Expr atom) => Mentions(atom, _dep);

    private static bool Mentions(Expr e, HashSet<string> names) => e switch
    {
        Var v => names.Contains(v.Name),
        Unary u => Mentions(u.Operand, names),
        Binary b => Mentions(b.Left, names) || Mentions(b.Right, names),
        Call c => c.Args.Any(a => Mentions(a, names)),
        IfExpr i => Mentions(i.Cond, names) || Mentions(i.Then, names) || Mentions(i.Else, names),
        Index i => Mentions(i.Array, names) || Mentions(i.At, names),
        FieldAccess f => Mentions(f.Target, names),
        ArrayLit a => a.Elems.Any(x => Mentions(x, names)),
        MatchExpr m => Mentions(m.Scrutinee, names) || m.Arms.Any(a => Mentions(a.Body, names)),
        _ => false,
    };

    private Var Emit(Expr rhs, Expr original, Ctx ctx)
    {
        var name = $"$v{++_n}";
        var dep = IsDep(rhs);
        var type = original.Type.Base.Subst(new Dictionary<string, TType>(), ctx.Dims);
        rhs.Span = _at;
        _nodes.Add(new Node(name, rhs, type, dep));
        _types[name] = type;
        if (dep) _dep.Add(name);
        return V(name);
    }

    // ---------- backward: vector-Jacobian products ----------

    private void Backward(Node node, Var g, Action<Expr, Expr> add)
    {
        var y = V(node.Name);
        switch (node.Rhs)
        {
            case Unary u:
                add(u.Operand, Neg(g));
                break;
            case Binary { Op: "+" } b: add(b.Left, g); add(b.Right, Copy(g)); break;
            case Binary { Op: "-" } b: add(b.Left, g); add(b.Right, Neg(g)); break;
            case Binary { Op: "*" } b: add(b.Left, Bin("*", g, Copy(b.Right))); add(b.Right, Bin("*", Copy(g), Copy(b.Left))); break;
            case Binary { Op: "/" } b:
                add(b.Left, Bin("/", g, Copy(b.Right)));
                add(b.Right, Neg(Bin("/", Bin("*", Copy(g), Copy(b.Left)), Bin("*", Copy(b.Right), Copy(b.Right)))));
                break;
            case Call c:
            {
                var a = c.Args;
                Expr A(int i) => Copy(a[i]);
                switch (c.Name)
                {
                    case "matmul":
                        add(a[0], B("matmul", g, B("transpose", A(1))));
                        add(a[1], B("matmul", B("transpose", A(0)), Copy(g)));
                        break;
                    case "add": add(a[0], g); add(a[1], Copy(g)); break;
                    case "sub": add(a[0], g); add(a[1], B("scale", Copy(g), F(-1.0))); break;
                    case "mul": add(a[0], B("mul", g, A(1))); add(a[1], B("mul", Copy(g), A(0))); break;
                    case "scale": add(a[0], B("scale", g, A(1))); add(a[1], B("sum", B("mul", Copy(g), A(0)))); break;
                    case "add_bias": add(a[0], g); add(a[1], B("sum_rows", Copy(g))); break;
                    case "relu": add(a[0], B("relu_grad", A(0), g)); break;
                    case "tanh": add(a[0], B("tanh_grad", y, g)); break;
                    case "sigmoid": add(a[0], B("sigmoid_grad", y, g)); break;
                    case "softmax": add(a[0], B("softmax_grad", y, g)); break;
                    case "transpose": add(a[0], B("transpose", g)); break;
                    case "reshape": add(a[0], Shaped("reshape", TypeOf(a[0]), g)); break;
                    case "sum": add(a[0], Shaped("full", TypeOf(a[0]), g)); break;
                    case "full": add(a[0], B("sum", g)); break;
                    case "to_f32" or "to_f64": add(a[0], B(TypeOf(a[0]).ElemType == ElemType.Float64 ? "to_f64" : "to_f32", g)); break;
                    default:
                        Fail($"'{c.Name}' has no derivative rule");
                        break;
                }
                break;
            }
            default:
                Fail("unsupported operation in differentiable code");
                break;
        }
    }

    private TType TypeOf(Expr atom) => atom is Var v && _types.TryGetValue(v.Name, out var t) ? t : atom.Type;

    private Expr Sum(List<Expr> terms, TType type) =>
        terms.Skip(1).Aggregate(terms[0], (acc, t) => type.Kind == TK.Float ? Bin("+", acc, t) : B("add", acc, t));

    private Expr Zero(TType t) => t.Kind == TK.Float ? F(0.0) : Shaped("full", t, F(0.0));

    // ---------- AST construction ----------

    private Var V(string name) => new(name) { Span = _at };
    private FloatLit F(double v) => new(v, v.ToString("0.0###############", System.Globalization.CultureInfo.InvariantCulture)) { Span = _at };
    private Binary Bin(string op, Expr a, Expr b) => new(op, a, b) { Span = _at };
    private Expr Neg(Expr a) => new Unary("-", a) { Span = _at };
    private Call B(string name, params Expr[] args) => new(name, [.. args], args.Select(_ => (string?)null).ToList()) { Span = _at };
    private Call Shaped(string name, TType shape, Expr arg) => new(name, [arg], [null]) { Span = _at, ShapeArg = shape };

    private Expr? Fail(string message, string? hint = null)
    {
        diags.Error("TN2015", _at, message, hint);
        _failed = true;
        return null;
    }

    private Expr Copy(Expr e) => Rewrite(e, _ => null, new Dictionary<string, Dim>());

    public static Expr DimExpr(Dim d, Span at) => d.Lit is { } v ? new IntLit(v) { Span = at }
        : d.Name != null ? new Var(d.Name) { Span = at }
        : new Binary(d.Op.ToString(), DimExpr(d.L!, at), DimExpr(d.R!, at)) { Span = at };

    /// <summary>Deep copy with variables and dimensions replaced. Copies are untyped; the checker types them again.</summary>
    public static Expr Rewrite(Expr e, Func<string, Expr?> vars, IReadOnlyDictionary<string, Dim> dims)
    {
        Expr R(Expr x) => Rewrite(x, vars, dims);
        var empty = new Dictionary<string, TType>();
        Expr r = e switch
        {
            IntLit i => new IntLit(i.Value),
            FloatLit f => new FloatLit(f.Value, f.Text),
            BoolLit b => new BoolLit(b.Value),
            UnitLit => new UnitLit(),
            Var { Kind: VarKind.Dim } v when dims.TryGetValue(v.Name, out var d) => DimExpr(d, v.Span),
            Var v => vars(v.Name) ?? new Var(v.Name),
            Unary u => new Unary(u.Op, R(u.Operand)),
            Binary b => new Binary(b.Op, R(b.Left), R(b.Right)),
            IfExpr i => new IfExpr(R(i.Cond), R(i.Then), R(i.Else)),
            Index i => new Index(R(i.Array), R(i.At)),
            FieldAccess f => new FieldAccess(R(f.Target), f.Field),
            ArrayLit a => new ArrayLit(a.Elems.Select(R).ToList()),
            TensorLit t => new TensorLit(t.Elem, t.Shape, t.Values, t.Texts),
            Call c => new Call(c.Name, c.Args.Select(R).ToList(), [.. c.ArgNames]) { ShapeArg = c.ShapeArg?.Subst(empty, dims) },
            MatchExpr m => new MatchExpr(R(m.Scrutinee), m.Arms.Select(a => (a.Pattern, R(a.Body))).ToList()),
            Quant q => new Quant
            {
                ForAll = q.ForAll, Kind = q.Kind, Binders = [.. q.Binders], Lo = q.Lo == null ? null : R(q.Lo), Hi = q.Hi == null ? null : R(q.Hi),
                Source = q.Source == null ? null : R(q.Source), Triggers = q.Triggers.Select(g => g.Select(R).ToList()).ToList(), Body = R(q.Body),
            },
            Hole h => new Hole(h.Name),
            _ => throw new InvalidOperationException(e.GetType().Name),
        };
        if (r.Span.End == 0) r.Span = e.Span;
        return r;
    }
}
