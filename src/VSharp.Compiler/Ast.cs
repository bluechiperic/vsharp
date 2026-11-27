using System.Reflection;
using System.Text.Json.Serialization;

namespace VSharp.Compiler;

/// <summary>A source range. <see cref="File"/> indexes the module's source files.</summary>
public readonly record struct Span(int Start, int End, int Line, int Col, int EndLine, int EndCol, int File = 0);

public sealed class Diagnostic
{
    public required string Code { get; init; }
    public required string Severity { get; init; }
    public required string Message { get; init; }
    public string? File { get; set; }
    [JsonIgnore] public int FileIndex { get; set; }
    public int Line { get; init; }
    public int Col { get; init; }
    public int EndLine { get; init; }
    public int EndCol { get; init; }
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public string? Hint { get; init; }
    /// <summary>For verification failures: "refuted" (a counterexample exists) or "unknown" (solver gave up).</summary>
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public string? Status { get; init; }
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public Dictionary<string, string>? Counterexample { get; init; }
    /// <summary>For typed holes: the variables in scope and their types.</summary>
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public Dictionary<string, string>? InScope { get; init; }
    /// <summary>For typed holes: what is known at the hole.</summary>
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public List<string>? Facts { get; init; }
    /// <summary>For typed holes: what the expression that fills the hole must satisfy.</summary>
    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] public List<string>? Obligations { get; init; }
}

public sealed class DiagnosticBag
{
    private readonly HashSet<(string, int, int, string)> _seen = [];
    public List<Diagnostic> Items { get; } = [];
    public bool HasErrors => Items.Any(d => d.Severity == "error");

    public void Error(string code, Span span, string message, string? hint = null) => Add("error", code, span, message, hint);
    public void Warning(string code, Span span, string message, string? hint = null) => Add("warning", code, span, message, hint);

    public void Add(string severity, string code, Span span, string message, string? hint = null,
        string? status = null, Dictionary<string, string>? counterexample = null)
    {
        if (!_seen.Add((code, span.File, span.Start, message))) return;
        Items.Add(new Diagnostic
        {
            Code = code, Severity = severity, Message = message, Hint = hint, Status = status, FileIndex = span.File,
            Counterexample = counterexample, Line = span.Line, Col = span.Col, EndLine = span.EndLine, EndCol = span.EndCol,
        });
    }

    public void Add(Diagnostic d)
    {
        if (_seen.Add((d.Code, d.FileIndex, d.Line * 100000 + d.Col, d.Message))) Items.Add(d);
    }
}

public sealed class CompileError(string code, Span span, string message, string? hint = null) : Exception(message)
{
    public string Code { get; } = code;
    public Span Span { get; } = span;
    public string? Hint { get; } = hint;
}

// ---------- Dimensions ----------

/// <summary>A tensor dimension: a positive integer literal, a dimension parameter, or a sum or product of dimensions.</summary>
public sealed class Dim
{
    public long? Lit { get; }
    public string? Name { get; }
    public char Op { get; }
    public Dim? L { get; }
    public Dim? R { get; }

    private Dim(long? lit, string? name, char op, Dim? l, Dim? r) { Lit = lit; Name = name; Op = op; L = l; R = r; }

    public static Dim Of(long v) => new(v, null, '\0', null, null);
    public static Dim Var(string name) => new(null, name, '\0', null, null);

    public static Dim Bin(char op, Dim l, Dim r)
    {
        if (l.Lit is { } a && r.Lit is { } b) return Of(op == '+' ? checked(a + b) : checked(a * b));
        return new(null, null, op, l, r);
    }

    public bool IsBareName => Name != null;

    public IEnumerable<string> Names()
    {
        if (Name != null) yield return Name;
        if (L != null) foreach (var n in L.Names()) yield return n;
        if (R != null) foreach (var n in R.Names()) yield return n;
    }

    public Dim Subst(IReadOnlyDictionary<string, Dim> map)
    {
        if (Name != null) return map.TryGetValue(Name, out var d) ? d : this;
        if (Lit != null) return this;
        return Bin(Op, L!.Subst(map), R!.Subst(map));
    }

    /// <summary>Canonical polynomial: monomial (sorted names joined by '*', "" for the constant) to coefficient.</summary>
    public SortedDictionary<string, long> Poly()
    {
        if (Lit is { } v) return new() { [""] = v };
        if (Name != null) return new() { [Name] = 1 };
        var (a, b) = (L!.Poly(), R!.Poly());
        var r = new SortedDictionary<string, long>(StringComparer.Ordinal);
        if (Op == '+')
        {
            foreach (var (k, c) in a) r[k] = r.GetValueOrDefault(k) + c;
            foreach (var (k, c) in b) r[k] = r.GetValueOrDefault(k) + c;
        }
        else
        {
            foreach (var (ka, ca) in a)
                foreach (var (kb, cb) in b)
                {
                    var k = string.Join("*", (ka + "*" + kb).Split('*', StringSplitOptions.RemoveEmptyEntries).Order(StringComparer.Ordinal));
                    r[k] = r.GetValueOrDefault(k) + checked(ca * cb);
                }
        }
        return r;
    }

    /// <summary>True when the two dimensions are the same polynomial, i.e. equal for every value of the parameters.</summary>
    public bool PolyEquals(Dim o) => Poly().SequenceEqual(o.Poly());

    public override string ToString() => Show(0);

    private string Show(int prec)
    {
        if (Lit != null) return Lit.Value.ToString();
        if (Name != null) return Name;
        var p = Op == '+' ? 1 : 2;
        var s = $"{L!.Show(p)} {Op} {R!.Show(p + (Op == '+' ? 0 : 0))}";
        return p < prec ? $"({s})" : s;
    }

    public static Dim Product(IEnumerable<Dim> dims) => dims.Aggregate(Of(1), (a, b) => Bin('*', a, b));
}

// ---------- Types ----------

public enum TK { Int, Bool, Unit, Float, Array, Tensor, Named, Param, Error, String, Date, Decimal, Int32, Map, Set }

public enum ElemType { Float32, Float64 }

public sealed class TType
{
    public TK Kind { get; private init; }
    public TType? Elem { get; private init; }
    public ElemType ElemType { get; private init; }
    public IReadOnlyList<Dim> Dims { get; private init; } = [];
    /// <summary>Type name for Named (resolved or not) and Param.</summary>
    public string? Name { get; private init; }
    public TypeDecl? Decl { get; private init; }
    public IReadOnlyList<TType> Args { get; private init; } = [];
    /// <summary>The refinement alias this type was written as, if any.</summary>
    public TypeDecl? Refine { get; private init; }
    public IReadOnlyList<TType> RefineArgs { get; private init; } = [];
    public Span Span { get; private init; }

    public static readonly TType Int = new() { Kind = TK.Int };
    public static readonly TType Bool = new() { Kind = TK.Bool };
    public static readonly TType Unit = new() { Kind = TK.Unit };
    public static readonly TType Float = new() { Kind = TK.Float };
    public static readonly TType Error = new() { Kind = TK.Error };
    public static readonly TType String = new() { Kind = TK.String };
    public static readonly TType Date = new() { Kind = TK.Date };
    public static readonly TType Decimal = new() { Kind = TK.Decimal };
    public static readonly TType Int32 = new() { Kind = TK.Int32 };
    public static TType ArrayOf(TType elem) => new() { Kind = TK.Array, Elem = elem };
    public static TType MapOf(TType key, TType value) => new() { Kind = TK.Map, Args = [key, value] };
    public static TType SetOf(TType elem) => new() { Kind = TK.Set, Elem = elem };
    public static TType Tensor(ElemType e, IReadOnlyList<Dim> dims) => new() { Kind = TK.Tensor, ElemType = e, Dims = dims };
    public static TType Unresolved(string name, IReadOnlyList<TType> args, Span span) => new() { Kind = TK.Named, Name = name, Args = args, Span = span };
    public static TType Named(TypeDecl decl, IReadOnlyList<TType> args) => new() { Kind = TK.Named, Name = decl.Name, Decl = decl, Args = args };
    public static TType Param(string name) => new() { Kind = TK.Param, Name = name };

    public TType WithRefine(TypeDecl r, IReadOnlyList<TType> args) => new()
    {
        Kind = Kind, Elem = Elem, ElemType = ElemType, Dims = Dims, Name = Name, Decl = Decl, Args = Args, Refine = r, RefineArgs = args,
    };

    public TType Base => Refine == null ? this : new() { Kind = Kind, Elem = Elem, ElemType = ElemType, Dims = Dims, Name = Name, Decl = Decl, Args = Args };

    public bool IsError => Kind == TK.Error;
    public bool IsScalar => Kind is TK.Int or TK.Bool or TK.Float;
    public bool IsIntegral => Kind is TK.Int or TK.Int32;
    /// <summary>Types with arithmetic: + - * / and unary minus.</summary>
    public bool IsNumeric => Kind is TK.Int or TK.Int32 or TK.Float or TK.Decimal;
    /// <summary>Types with a total order: &lt; &lt;= &gt; &gt;=, and sort keys.</summary>
    public bool IsOrdered => Kind is TK.Int or TK.Int32 or TK.Float or TK.Decimal or TK.Date;
    public TType Key => Args[0];
    public TType Value => Args[1];

    /// <summary>
    /// Values whose run-time equality (Equals) agrees with equality in the logic, so they can be compared with '==' in
    /// code and used as map keys and set elements. Floats are excluded (NaN), and so are containers and interface
    /// values, whose run-time equality depends on the implementation.
    /// </summary>
    public bool IsEquatable => Kind switch
    {
        TK.Int or TK.Int32 or TK.Bool or TK.String or TK.Date or TK.Decimal or TK.Param or TK.Error => true,
        TK.Named => !DeepContains(t => t.Kind is TK.Array or TK.Tensor or TK.Map or TK.Set or TK.Float || t.IsInterface),
        _ => false,
    };

    public bool IsInterface => Kind == TK.Named && Decl?.Kind == TypeKind.Interface;
    public bool IsClass => Kind == TK.Named && Decl is { IsClass: true };

    /// <summary>Like <see cref="Contains"/>, but also looks inside the fields of records and union cases.</summary>
    public bool DeepContains(Func<TType, bool> pred) => DeepContains(pred, []);

    private bool DeepContains(Func<TType, bool> pred, HashSet<string> seen)
    {
        if (pred(this) || (Elem?.DeepContains(pred, seen) ?? false) || Args.Any(a => a.DeepContains(pred, seen))) return true;
        return Kind == TK.Named && Decl != null && seen.Add(Decl.Name)
            && Decl.Fields.Concat(Decl.Cases.SelectMany(c => c.Fields)).Any(f => f.Type.DeepContains(pred, seen));
    }

    /// <summary>Structural equality. Refinements are ignored; dimensions are compared as polynomials.</summary>
    public bool Same(TType o)
    {
        if (IsError || o.IsError) return true;
        if (Kind != o.Kind) return false;
        return Kind switch
        {
            TK.Array or TK.Set => Elem!.Same(o.Elem!),
            TK.Map => Key.Same(o.Key) && Value.Same(o.Value),
            TK.Tensor => ElemType == o.ElemType && Dims.Count == o.Dims.Count && Dims.Zip(o.Dims).All(p => p.First.PolyEquals(p.Second)),
            TK.Named => Name == o.Name && Args.Count == o.Args.Count && Args.Zip(o.Args).All(p => p.First.Same(p.Second)),
            TK.Param => Name == o.Name,
            _ => true,
        };
    }

    public bool Contains(Func<TType, bool> pred) =>
        pred(this) || (Elem?.Contains(pred) ?? false) || Args.Any(a => a.Contains(pred)) || RefineArgs.Any(a => a.Contains(pred));

    public bool HasParams => Contains(t => t.Kind == TK.Param) || (Kind == TK.Tensor && Dims.Any(d => d.Names().Any()));

    public TType Subst(IReadOnlyDictionary<string, TType> types, IReadOnlyDictionary<string, Dim> dims)
    {
        switch (Kind)
        {
            case TK.Param:
                return types.TryGetValue(Name!, out var t) ? (Refine != null && t.Refine == null ? t.WithRefine(Refine, RefineArgs) : t) : this;
            case TK.Array:
                return Keep(ArrayOf(Elem!.Subst(types, dims)), types, dims);
            case TK.Set:
                return SetOf(Elem!.Subst(types, dims));
            case TK.Map:
                return MapOf(Key.Subst(types, dims), Value.Subst(types, dims));
            case TK.Tensor:
                return Keep(Tensor(ElemType, Dims.Select(d => d.Subst(dims)).ToList()), types, dims);
            case TK.Named when Decl != null:
                return Keep(Named(Decl, Args.Select(a => a.Subst(types, dims)).ToList()), types, dims);
            default:
                return this;
        }
    }

    private TType Keep(TType t, IReadOnlyDictionary<string, TType> types, IReadOnlyDictionary<string, Dim> dims) =>
        Refine == null ? t : t.WithRefine(Refine, RefineArgs.Select(a => a.Subst(types, dims)).ToList());

    public override string ToString()
    {
        if (Refine != null) return RefineArgs.Count == 0 ? Refine.Name : $"{Refine.Name}[{string.Join(", ", RefineArgs)}]";
        return Kind switch
        {
            TK.Array => $"Array[{Elem}]",
            TK.Set => $"Set[{Elem}]",
            TK.Map => $"Map[{Key}, {Value}]",
            TK.Tensor => $"Tensor[{(ElemType == ElemType.Float64 ? "Float64; " : "")}{string.Join(", ", Dims)}]",
            TK.Named or TK.Param => Args.Count == 0 ? Name! : $"{Name}[{string.Join(", ", Args)}]",
            TK.Error => "<error>",
            _ => Kind.ToString(),
        };
    }
}

// ---------- Expressions ----------

public abstract class Expr
{
    public Span Span { get; set; }
    public TType Type { get; set; } = TType.Error;
    /// <summary>A class value used where an interface it implements is expected: the interface it is converted to.</summary>
    public TypeDecl? Upcast { get; set; }
    /// <summary>Dimension equalities the checker could not decide syntactically; the verifier proves them here.</summary>
    public List<(Dim A, Dim B)> ShapeEqs { get; } = [];
    /// <summary>The expression is interpreted in the real-number tensor model (it involves tensor elements).</summary>
    public bool RealModel { get; set; }
}

public sealed class IntLit(long value) : Expr { public long Value { get; } = value; }
public sealed class FloatLit(double value, string text) : Expr
{
    public double Value { get; } = value;
    public string Text { get; } = text;
}
public sealed class BoolLit(bool value) : Expr { public bool Value { get; } = value; }
public sealed class UnitLit : Expr;

public sealed class DecLit(decimal value, string text) : Expr
{
    public decimal Value { get; } = value;
    public string Text { get; } = text;
}

public sealed class StrLit(string value) : Expr { public string Value { get; } = value; }

/// <summary>An interpolated string: literal parts (<see cref="StrLit"/>) and embedded expressions, concatenated.</summary>
public sealed class Interp(List<Expr> parts) : Expr { public List<Expr> Parts { get; } = parts; }

/// <summary>'x => e' or '(acc, x) => e'. Only allowed as an argument of a collection builtin, which inlines it.</summary>
public sealed class Lambda(List<string> parameters, Expr body) : Expr
{
    public List<string> Params { get; } = parameters;
    public Expr Body { get; } = body;
    public List<TType> ParamTypes { get; set; } = [];
}

/// <summary>'r with { f: e, ... }': a copy of record r with some fields replaced.</summary>
public sealed class WithExpr(Expr target, List<(string Field, Expr Value)> updates) : Expr
{
    public Expr Target { get; } = target;
    public List<(string Field, Expr Value)> Updates { get; } = updates;
    public List<FieldDecl?> Resolved { get; } = [];
}

public enum VarKind { Unknown, Local, Param, Dim, Bound, Elem, Result, Self, Ctor, Const }

public sealed class Var(string name) : Expr
{
    public string Name { get; } = name;
    public VarKind Kind { get; set; }
    /// <summary>For a nullary union case used as a value.</summary>
    public CaseDecl? Ctor { get; set; }
    public ConstDecl? Const { get; set; }
    public Dictionary<string, TType> TypeArgs { get; set; } = [];
}

public sealed class Unary(string op, Expr operand) : Expr { public string Op { get; } = op; public Expr Operand { get; } = operand; }

public sealed class Binary(string op, Expr left, Expr right) : Expr
{
    public string Op { get; } = op;
    public Expr Left { get; } = left;
    public Expr Right { get; } = right;
}

public sealed class IfExpr(Expr cond, Expr then, Expr @else) : Expr
{
    public Expr Cond { get; } = cond;
    public Expr Then { get; } = then;
    public Expr Else { get; } = @else;
}

public sealed class Call(string name, List<Expr> args, List<string?> argNames) : Expr
{
    public string Name { get; } = name;
    public List<Expr> Args { get; } = args;
    /// <summary>Argument names as written; null entries are positional.</summary>
    public List<string?> ArgNames { get; } = argNames;
    /// <summary>Explicit shape for 'reshape[...]' and 'full[...]'.</summary>
    public TType? ShapeArg { get; set; }
    public FnDecl? Target { get; set; }
    public CaseDecl? Case { get; set; }
    public TypeDecl? Record { get; set; }
    public Dictionary<string, TType> TypeArgs { get; set; } = [];
    public Dictionary<string, Dim> DimArgs { get; set; } = [];
    /// <summary>'x.name(args)': a method call. The receiver is Args[0] and <see cref="Name"/> is the method's own name.</summary>
    public bool Method { get; init; }
    /// <summary>'await f(...)', which may only be the whole value of a let, var, set, return or do statement.</summary>
    public bool Awaited { get; set; }
    /// <summary>The exception built by 'throw E(...)'.</summary>
    public ExceptionDecl? Exception { get; set; }
    /// <summary>Where each exception the callee may throw goes: one site per 'throws' clause of the callee.</summary>
    public List<ThrowSite> ThrowSites { get; } = [];
    public bool IsBuiltin => Target == null && Case == null && Record == null && Exception == null;
}

public sealed class Index(Expr array, Expr at) : Expr { public Expr Array { get; } = array; public Expr At { get; } = at; }

public sealed class FieldAccess(Expr target, string field) : Expr
{
    public Expr Target { get; } = target;
    public string Field { get; } = field;
    public FieldDecl? Resolved { get; set; }
}

public sealed class ArrayLit(List<Expr> elems) : Expr { public List<Expr> Elems { get; } = elems; }

public sealed class TensorLit(ElemType elem, List<long> shape, List<double> values, List<string> texts) : Expr
{
    public ElemType Elem { get; } = elem;
    public List<long> Shape { get; } = shape;
    public List<double> Values { get; } = values;
    /// <summary>The values as written, so the formatter reproduces them exactly.</summary>
    public List<string> Texts { get; } = texts;
}

public enum QuantKind { Range, Typed, Elems }

public sealed class Quant : Expr
{
    public required bool ForAll { get; init; }
    public required QuantKind Kind { get; init; }
    public required List<(string Name, TType Type)> Binders { get; init; }
    public Expr? Lo { get; init; }
    public Expr? Hi { get; init; }
    /// <summary>For 'forall e in elems(t)': the tensor.</summary>
    public Expr? Source { get; init; }
    public List<List<Expr>> Triggers { get; init; } = [];
    public required Expr Body { get; init; }
}

public sealed class Pattern
{
    /// <summary>Case name, or null for the wildcard '_' (and for literal and or-patterns).</summary>
    public string? Case { get; init; }
    public List<string> Binders { get; init; } = [];
    public Span Span { get; init; }
    public CaseDecl? Resolved { get; set; }
    /// <summary>A literal pattern: an Int, String, Bool or Decimal literal compared with '=='.</summary>
    public Expr? Literal { get; init; }
    /// <summary>An or-pattern 'p1 | p2 | ...'; its alternatives bind no names.</summary>
    public List<Pattern>? Alternatives { get; init; }

    public bool IsWildcard => Case == null && Literal == null && Alternatives == null;
}

public sealed class MatchExpr(Expr scrutinee, List<(Pattern Pattern, Expr Body)> arms) : Expr
{
    public Expr Scrutinee { get; } = scrutinee;
    public List<(Pattern Pattern, Expr Body)> Arms { get; } = arms;
}

public sealed class Hole(string name) : Expr { public string Name { get; } = name; }

// ---------- Statements ----------

public abstract class Stmt
{
    public Span Span { get; set; }
    /// <summary>Ghost statements are verified and then erased; they never run.</summary>
    public bool Ghost { get; set; }
}

public sealed class Let(string name, bool mutable, TType? annotation, Expr init) : Stmt
{
    public string Name { get; } = name;
    public bool Mutable { get; } = mutable;
    public TType? Annotation { get; set; } = annotation;
    public Expr Init { get; } = init;
    public TType VarType { get; set; } = TType.Error;
}
public sealed class Set(string name, Expr value) : Stmt
{
    public string Name { get; } = name;
    public Expr Value { get; } = value;
    public TType VarType { get; set; } = TType.Error;
}
public sealed class If(Expr cond, List<Stmt> then, List<Stmt>? @else) : Stmt
{
    public Expr Cond { get; } = cond;
    public List<Stmt> Then { get; } = then;
    public List<Stmt>? Else { get; } = @else;
}
public sealed class While(Expr cond, List<Expr> invariants, List<Expr> decreases, List<Stmt> body) : Stmt
{
    public Expr Cond { get; } = cond;
    public List<Expr> Invariants { get; } = invariants;
    public List<Expr> Decreases { get; } = decreases;
    public List<Stmt> Body { get; } = body;
}
/// <summary>
/// 'for i in lo..hi', 'for x in a' or 'for i, x in a'. The index runs from lo (or 0) up to hi (or len(a)); in the
/// invariants it is the number of iterations completed. Termination is automatic.
/// </summary>
public sealed class For : Stmt
{
    public string? Index { get; init; }
    public string? Elem { get; init; }
    public Expr? Source { get; init; }
    public Expr? Lo { get; init; }
    public Expr? Hi { get; init; }
    public List<Expr> Invariants { get; init; } = [];
    public List<Stmt> Body { get; init; } = [];
    public TType ElemType { get; set; } = TType.Error;
    /// <summary>The index variable's name, invented when the source does not name it.</summary>
    public string IndexName => Index ?? $"for!{Span.Start}";
}
public sealed class Break : Stmt;
public sealed class Continue : Stmt;
public sealed class Return(Expr value) : Stmt { public Expr Value { get; } = value; }
public sealed class Assert(Expr cond) : Stmt { public Expr Cond { get; } = cond; }
public sealed class Print(Expr value) : Stmt { public Expr Value { get; } = value; }
public sealed class Do(Expr call) : Stmt { public Expr Call { get; } = call; }
public sealed class MatchStmt(Expr scrutinee, List<(Pattern Pattern, List<Stmt> Body)> arms) : Stmt
{
    public Expr Scrutinee { get; } = scrutinee;
    public List<(Pattern Pattern, List<Stmt> Body)> Arms { get; } = arms;
}

/// <summary>'throw E(args)'.</summary>
public sealed class Throw(Call value) : Stmt
{
    public Call Value { get; } = value;
    public ThrowSite? Site { get; set; }
}

/// <summary>'try { ... } catch E(x, ...) { ... } ...'. A catch body runs after the try block, outside it.</summary>
public sealed class Try(List<Stmt> body, List<Catch> catches) : Stmt
{
    public List<Stmt> Body { get; } = body;
    public List<Catch> Catches { get; } = catches;
}

public sealed class Catch
{
    public required string Name { get; init; }
    public required Span Span { get; init; }
    /// <summary>Names for the exception's fields, in order ('_' skips one); empty when the fields are not needed.</summary>
    public List<string> Binders { get; init; } = [];
    public List<Stmt> Body { get; init; } = [];
    public ExceptionDecl? Decl { get; set; }
}

/// <summary>
/// A point where an exception may be thrown: a 'throw' statement, or a call to a function that declares it. The checker
/// resolves where it goes: the catch clauses that may receive it, and whether it can leave the function.
/// </summary>
public sealed class ThrowSite
{
    public required ExceptionDecl Exception { get; init; }
    /// <summary>For a call: the callee's clause, whose 'when' condition is necessary for the throw.</summary>
    public ThrowsClause? Clause { get; init; }
    public List<Catch> Catches { get; } = [];
    public bool Escapes { get; set; }
}

// ---------- Declarations ----------

/// <summary>What a .NET attribute is attached to, in the emitted assembly.</summary>
public enum AttrTarget { Class, Interface, Property, Method, Parameter }

/// <summary>
/// '@Name' or '@Name(args)': a .NET attribute, written into the assembly and ignored by the verifier. Arguments are
/// literals, enum members and arrays of those; a named argument sets a property or field of the attribute.
/// </summary>
public sealed class Attr
{
    public required string Name { get; init; }
    public required Span Span { get; init; }
    public List<Expr> Args { get; init; } = [];
    public List<string?> ArgNames { get; init; } = [];
    public bool HasParens { get; init; }
    public ConstructorInfo? Ctor { get; set; }
    public object?[] CtorArgs { get; set; } = [];
    public List<(MemberInfo Member, object? Value)> Named { get; } = [];
}

public sealed record Param(string Name, TType Type, Span Span)
{
    public TType Type { get; set; } = Type;
    public List<Attr> Attrs { get; init; } = [];
}

public enum FnKind { Fn, Spec, Lemma, Extern, Grad }

public sealed class FnDecl
{
    public required string Name { get; init; }
    public required Span NameSpan { get; init; }
    public FnKind Kind { get; set; } = FnKind.Fn;
    public int Start { get; init; }
    /// <summary>Names in the '[...]' after the function name, in order. The checker splits them into dimension and type parameters.</summary>
    public List<string> Generics { get; } = [];
    public List<string> DimParams { get; } = [];
    public List<string> TypeParams { get; } = [];
    public List<Param> Params { get; } = [];
    public TType Ret { get; set; } = TType.Unit;
    public List<Expr> Requires { get; } = [];
    public List<Expr> Ensures { get; } = [];
    public List<Expr> Decreases { get; } = [];
    public SortedSet<string> Effects { get; } = new(StringComparer.Ordinal);
    public bool Total { get; set; }
    public List<Stmt> Body { get; set; } = [];
    public Expr? BodyExpr { get; set; }
    public string? ExternTarget { get; set; }
    public MethodInfo? ExternMethod { get; set; }
    public string? GradOf { get; set; }
    public string? GradWrt { get; set; }
    public Span EndSpan { get; set; }
    public bool Prelude { get; set; }
    /// <summary>Functions referenced from the body, the contract or the refinement types of the signature.</summary>
    public HashSet<FnDecl> Calls { get; } = [];
    /// <summary>Strongly connected component of the call graph; members may call each other recursively.</summary>
    public int Scc { get; set; } = -1;
    public bool Recursive { get; set; }
    public List<Attr> Attrs { get; init; } = [];
    /// <summary>For a method: the class or interface that declares it. Its <see cref="Name"/> is 'Owner.member'.</summary>
    public TypeDecl? Owner { get; set; }
    /// <summary>For a method: its name within the class or interface.</summary>
    public string? Member { get; init; }
    /// <summary>For a class method: the interface method it implements, whose contract it inherits.</summary>
    public FnDecl? Implements { get; set; }
    public List<ThrowsClause> Throws { get; } = [];

    /// <summary>The 'throws' clauses in force: its own and those inherited from the interface method it implements.</summary>
    public IEnumerable<ThrowsClause> AllThrows => Throws.Concat(Implements?.Throws ?? []);
    /// <summary>No effects and no exceptions: the function denotes a mathematical function, usable in specifications.</summary>
    public bool IsPure => Effects.Count == 0 && Throws.Count == 0;
    /// <summary>Compiled to a method returning Task or Task&lt;T&gt;; calls to it are awaited.</summary>
    public bool IsAsync => Effects.Contains("async");
    public bool IsGhost => Kind is FnKind.Spec or FnKind.Lemma;
    public bool IsExecutable => Kind is FnKind.Fn or FnKind.Grad or FnKind.Extern;
    public bool IsGeneric => TypeParams.Count > 0;
    public bool IsMethod => Owner != null;
    /// <summary>An interface method: a contract without a body, dispatched at run time.</summary>
    public bool IsAbstract => Owner?.Kind == TypeKind.Interface;
}

public enum TypeKind { Record, Union, Refinement, Interface }

public sealed class FieldDecl(string name, TType type, Span span)
{
    public string Name { get; } = name;
    public TType Type { get; set; } = type;
    public Span Span { get; } = span;
    public int Index { get; set; }
    public List<Attr> Attrs { get; init; } = [];
}

public sealed class CaseDecl
{
    public required string Name { get; init; }
    public required Span Span { get; init; }
    public List<FieldDecl> Fields { get; } = [];
    public TypeDecl Owner { get; set; } = null!;
    public int Index { get; set; }
}

public sealed class TypeDecl
{
    public required string Name { get; init; }
    public required Span NameSpan { get; init; }
    public required TypeKind Kind { get; init; }
    public int Start { get; init; }
    public List<string> TypeParams { get; } = [];
    public List<FieldDecl> Fields { get; } = [];
    public List<CaseDecl> Cases { get; } = [];
    public TType? Base { get; set; }
    public Expr? Pred { get; set; }
    public bool Prelude { get; set; }
    /// <summary>Functions called by the refinement predicate or the class invariants.</summary>
    public HashSet<FnDecl> Calls { get; } = [];
    public List<Attr> Attrs { get; init; } = [];
    /// <summary>A class: a record with methods, invariants and interfaces. Its <see cref="Kind"/> is Record.</summary>
    public bool IsClass { get; init; }
    /// <summary>The methods of a class or interface.</summary>
    public List<FnDecl> Methods { get; } = [];
    public List<Expr> Invariants { get; } = [];
    /// <summary>The interfaces a class implements, as written, and once resolved.</summary>
    public List<(string Name, Span Span)> ImplementsNames { get; } = [];
    public List<TypeDecl> Interfaces { get; } = [];
    public Span EndSpan { get; set; }
}

/// <summary>
/// 'exception E(fields)': a sealed .NET exception class with those fields, or 'exception E from "Ns.Type"': an existing
/// .NET exception type, whose one field is its message.
/// </summary>
public sealed class ExceptionDecl
{
    public required string Name { get; init; }
    public required Span NameSpan { get; init; }
    public int Start { get; init; }
    public List<FieldDecl> Fields { get; } = [];
    public List<Attr> Attrs { get; init; } = [];
    public string? ClrName { get; init; }
    public Type? Clr { get; set; }
    public bool IsExtern => ClrName != null;

    /// <summary>Whether a catch or 'throws' clause for this exception also covers <paramref name="other"/>, as .NET catch clauses do.</summary>
    public bool Covers(ExceptionDecl other) => this == other || Clr != null && other.Clr != null && Clr.IsAssignableFrom(other.Clr);
    /// <summary>Whether a thrown <paramref name="other"/> might be an instance of this exception, or the reverse.</summary>
    public bool Overlaps(ExceptionDecl other) => Covers(other) || other.Covers(this);
}

/// <summary>'throws E' or 'throws E when cond': the function may throw E, and only when cond held on entry.</summary>
public sealed class ThrowsClause
{
    public required string Name { get; init; }
    public required Span Span { get; init; }
    public Expr? When { get; init; }
    public ExceptionDecl? Decl { get; set; }
}

/// <summary>'const NAME: T = e': a named value, inlined where it is used.</summary>
public sealed class ConstDecl
{
    public required string Name { get; init; }
    public required Span NameSpan { get; init; }
    public required TType Type { get; set; }
    public required Expr Value { get; init; }
    public int Start { get; init; }
}

public sealed record Comment(int Start, int Line, string Text, bool Trailing);

public sealed class ModuleDecl
{
    public required string Name { get; init; }
    public List<TypeDecl> Types { get; } = [];
    public List<FnDecl> Fns { get; } = [];
    public List<ConstDecl> Consts { get; } = [];
    public List<ExceptionDecl> Exceptions { get; } = [];
    public List<Comment> Comments { get; set; } = [];
    public List<Hole> Holes { get; } = [];
    public bool TotalByDefault { get; set; }
    public Span NameSpan { get; set; }
    /// <summary>'use Namespace': namespaces searched for the short names of attributes.</summary>
    public List<(string Namespace, Span Span, int Start)> Uses { get; } = [];
}
