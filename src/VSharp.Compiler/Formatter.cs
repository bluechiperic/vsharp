using System.Text;

namespace VSharp.Compiler;

/// <summary>
/// The canonical layout of V# source. Formatting is a function of the syntax tree and the comments alone, so two
/// programs with the same meaning and comments format identically, and formatting is idempotent.
/// </summary>
public sealed class Formatter
{
    private const int Width = 100;
    /// <summary>A call longer than this puts one argument per line. It depends only on the call, never on its column, so layout is canonical.</summary>
    private const int CallWidth = 80;

    private readonly string[] _sourceLines;
    private readonly List<Comment> _comments;
    private int _nextComment;
    private readonly List<string> _out = [];
    private readonly StringBuilder _line = new();
    private int _indent;

    private Formatter(string source, List<Comment> comments)
    {
        _sourceLines = source.Replace("\r\n", "\n").Split('\n');
        _comments = comments;
    }

    private bool _sig;
    private int _bodyEnd;

    public static string Format(string source) => Run(source, sig: false);

    /// <summary>The module's interface: types, signatures, contracts and spec function bodies, without executable bodies.</summary>
    public static string Signatures(string source) => Run(source, sig: true);

    private static string Run(string source, bool sig)
    {
        var tokens = Lexer.Lex(source, out var comments);
        var module = new Parser(tokens).ParseModule();
        var f = new Formatter(source, comments) { _sig = sig };
        f.Module(module);
        return string.Join("\n", f._out).TrimEnd() + "\n";
    }

    // ---------- lines and comments ----------

    // Expressions that span lines align their continuation lines to a column that is only known once the whole line is
    // assembled, so they are rendered with these markers and Line() resolves them.
    private const char PushAlign = '\u0002';
    private const char PopAlign = '\u0003';
    private const char AlignedLine = '\u0001';

    private void Line(string text)
    {
        if (text.Length == 0) { _out.Add(""); return; }
        var full = new string(' ', 2 * _indent) + text;
        if (!full.Contains(PushAlign)) { _out.Add(full); return; }
        var sb = new StringBuilder();
        var col = 0;
        var stack = new Stack<int>();
        foreach (var ch in full)
        {
            switch (ch)
            {
                case PushAlign: stack.Push(col); continue;
                case PopAlign: stack.Pop(); continue;
                case AlignedLine: sb.Append('\n').Append(' ', stack.Peek()); col = stack.Peek(); continue;
                default: sb.Append(ch); col++; continue;
            }
        }
        _out.Add(sb.ToString());
    }

    private int LineOf(int offset)
    {
        var (line, seen) = (1, 0);
        foreach (var l in _sourceLines)
        {
            if (seen + l.Length + 1 > offset) return line;
            seen += l.Length + 1;
            line++;
        }
        return line;
    }

    private void TrailingComments(int pos)
    {
        while (_nextComment < _comments.Count && _comments[_nextComment].Start < pos && _comments[_nextComment].Trailing && _out.Count > 0)
            _out[^1] += " " + _comments[_nextComment++].Text;
    }

    private bool BlankBefore(int line) => line >= 2 && line - 2 < _sourceLines.Length && _sourceLines[line - 2].Trim().Length == 0;

    private void Blank()
    {
        if (_out.Count > 0 && _out[^1].Length != 0 && !_out[^1].TrimEnd().EndsWith('{')) _out.Add("");
    }

    /// <summary>Emits the comments that precede source position <paramref name="pos"/>.</summary>
    private void Comments(int pos, bool keepBlank = true)
    {
        while (_nextComment < _comments.Count && _comments[_nextComment].Start < pos)
        {
            var c = _comments[_nextComment++];
            if (c.Trailing && _out.Count > 0 && _out[^1].Length > 0) { _out[^1] += " " + c.Text; continue; }
            if (keepBlank && BlankBefore(c.Line)) Blank();
            Line(c.Text);
        }
    }

    // ---------- declarations ----------

    private void Module(ModuleDecl m)
    {
        var decls = m.Types.Select(t => (t.Start, (object)t))
            .Concat(m.Fns.Select(f => (f.Start, (object)f)))
            .Concat(m.Consts.Select(c => (c.Start, (object)c)))
            .Concat(m.Exceptions.Select(e => (e.Start, (object)e)))
            .Concat(m.Uses.Select(u => (u.Start, (object)u.Namespace)))
            .OrderBy(d => d.Start).ToList();
        var (headerPos, headerLine) = FindModuleKeyword();
        Comments(headerPos);
        if (BlankBefore(headerLine)) Blank();
        Line(m.TotalByDefault ? $"module {m.Name} total" : $"module {m.Name}");
        var previousOneLine = false;
        foreach (var (start, d) in decls)
        {
            if (_sig) while (_nextComment < _comments.Count && _comments[_nextComment].Start < _bodyEnd) _nextComment++;
            TrailingComments(start);
            _out.Add("");
            var blankAt = _out.Count - 1;
            var commentsBefore = _nextComment;
            Comments(start, keepBlank: false);
            var first = _out.Count;
            if (d is TypeDecl t) TypeDecl(t);
            else if (d is ConstDecl c) Line($"const {c.Name}: {Type(c.Type)} = {Expr(c.Value)}");
            else if (d is string ns) Line($"use {ns}");
            else if (d is ExceptionDecl e) Exception(e);
            else Fn((FnDecl)d);
            var oneLine = _out.Count == first + 1 && !_out[first].Contains('\n');
            // A run of one-line declarations (grad definitions, externs, small types) stays together if it was together.
            if (previousOneLine && oneLine && commentsBefore == _nextComment && !BlankBefore(LineOf(start))) _out.RemoveAt(blankAt);
            previousOneLine = oneLine;
        }
        if (_sig) while (_nextComment < _comments.Count && _comments[_nextComment].Start < _bodyEnd) _nextComment++;
        Comments(int.MaxValue);
    }

    private (int Offset, int Line) FindModuleKeyword()
    {
        var offset = 0;
        for (var i = 0; i < _sourceLines.Length; i++)
        {
            var l = _sourceLines[i];
            var trimmed = l.TrimStart();
            if (trimmed.StartsWith("module ", StringComparison.Ordinal)) return (offset + (l.Length - trimmed.Length), i + 1);
            offset += l.Length + 1;
        }
        return (0, 1);
    }

    private static string Type(TType t) => t.ToString();

    private string Attr(Attr a)
    {
        if (!a.HasParens) return "@" + a.Name;
        var args = a.Args.Select((x, k) => a.ArgNames[k] is { } n ? $"{n}: {Expr(x)}" : Expr(x));
        return $"@{a.Name}({string.Join(", ", args)})";
    }

    /// <summary>Attributes of a declaration, one per line above it.</summary>
    private void Attrs(List<Attr> attrs)
    {
        foreach (var a in attrs) Line(Attr(a));
    }

    /// <summary>Attributes of a field or parameter, inline before it.</summary>
    private string Inline(List<Attr> attrs) => string.Concat(attrs.Select(a => Attr(a) + " "));

    private void TypeDecl(TypeDecl t)
    {
        Attrs(t.Attrs);
        if (t.IsClass || t.Kind == TypeKind.Interface)
        {
            ClassOrInterface(t);
            return;
        }
        var head = $"type {t.Name}{(t.TypeParams.Count > 0 ? $"[{string.Join(", ", t.TypeParams)}]" : "")} =";
        switch (t.Kind)
        {
            case TypeKind.Record:
            {
                var flat = $"{head} {{ {string.Join(", ", t.Fields.Select(Field))} }}".Replace("{  }", "{}");
                if (flat.Length <= Width || t.Fields.Count < 2) { Line(flat); break; }
                Line(head + " {");
                _indent++;
                for (var k = 0; k < t.Fields.Count; k++) Line(Field(t.Fields[k]) + (k < t.Fields.Count - 1 ? "," : ""));
                _indent--;
                Line("}");
                break;
            }
            case TypeKind.Refinement:
                Line($"{head} {Type(t.Base!)} where {Expr(t.Pred!)}");
                break;
            default:
                var cases = t.Cases.Select(c => c.Fields.Count == 0 ? $"| {c.Name}" : $"| {c.Name}({string.Join(", ", c.Fields.Select(Field))})").ToList();
                var one = $"{head} {string.Join(" ", cases)}";
                if (one.Length <= Width) { Line(one); break; }
                Line(head);
                _indent++;
                foreach (var c in cases) Line(c);
                _indent--;
                break;
        }
    }

    /// <summary>
    /// A class: its fields in the header (one per line if they do not fit), then invariants, then methods, separated
    /// by blank lines. An interface lists its methods the same way.
    /// </summary>
    private void ClassOrInterface(TypeDecl t)
    {
        var implements = t.ImplementsNames.Count > 0 ? " implements " + string.Join(", ", t.ImplementsNames.Select(n => n.Name)) : "";
        var empty = t.Invariants.Count == 0 && t.Methods.Count == 0 && !_comments.Skip(_nextComment).Any(c => c.Start < t.EndSpan.Start);
        var open = empty ? " {}" : " {";
        if (t.Kind == TypeKind.Interface) Line($"interface {t.Name}{open}");
        else
        {
            var flat = $"class {t.Name}({string.Join(", ", t.Fields.Select(Field))}){implements}{open}";
            if (flat.Length + 2 * _indent <= Width || t.Fields.Count < 2) Line(flat);
            else
            {
                Line($"class {t.Name}(");
                _indent++;
                for (var k = 0; k < t.Fields.Count; k++) Line(Field(t.Fields[k]) + (k < t.Fields.Count - 1 ? "," : ""));
                _indent--;
                Line($"){implements}{open}");
            }
        }
        if (empty) return;
        _indent++;
        foreach (var inv in t.Invariants) Clause("invariant", inv);
        foreach (var m in t.Methods)
        {
            if (_sig) while (_nextComment < _comments.Count && _comments[_nextComment].Start < _bodyEnd) _nextComment++;
            TrailingComments(m.Start);
            Blank();
            Comments(m.Start, keepBlank: false);
            Fn(m);
        }
        if (_sig) while (_nextComment < _comments.Count && _comments[_nextComment].Start < _bodyEnd) _nextComment++;
        Comments(t.EndSpan.Start);
        _indent--;
        Line("}");
    }

    private string Field(FieldDecl f) => $"{Inline(f.Attrs)}{f.Name}: {Type(f.Type)}";

    private void Exception(ExceptionDecl e)
    {
        Attrs(e.Attrs);
        if (e.IsExtern) Line($"exception {e.Name} from \"{e.ClrName}\"");
        else if (e.Fields.Count == 0) Line($"exception {e.Name}");
        else Line($"exception {e.Name}({string.Join(", ", e.Fields.Select(Field))})");
    }

    private void ThrowsClause(ThrowsClause t)
    {
        if (t.When == null) Line($"throws {t.Name}");
        else
        {
            Comments(t.When.Span.Start);
            Line($"throws {t.Name} when {Expr(t.When)}");
        }
    }

    private void Fn(FnDecl f)
    {
        var prefix = f.Kind switch { FnKind.Spec => "spec fn", FnKind.Lemma => "lemma fn", FnKind.Extern => "extern fn", _ => "fn" };
        if (f.Kind == FnKind.Grad)
        {
            Line($"fn {f.Name} = grad {f.GradOf} wrt {f.GradWrt}");
            return;
        }
        Attrs(f.Attrs);
        var generics = f.Generics.Count > 0 ? $"[{string.Join(", ", f.Generics)}]" : "";
        var ret = f.Kind == FnKind.Lemma && f.Ret.Kind == TK.Unit ? "" : $" -> {Type(f.Ret)}";
        var ps = f.Params.Select((p, k) => k == 0 && f.Owner != null ? "self" : $"{Inline(p.Attrs)}{p.Name}: {Type(p.Type)}");
        var sig = $"{prefix} {f.Member ?? f.Name}{generics}({string.Join(", ", ps)}){ret}";
        if (f.Effects.Count > 0) sig += " effects " + string.Join(", ", f.Effects);
        if (f.Total) sig += " total";
        var clauses = f.Requires.Count + f.Ensures.Count + f.Throws.Count + f.Decreases.Count > 0;
        var noBody = _sig && f.Kind is FnKind.Fn or FnKind.Lemma || f.Owner?.Kind == TypeKind.Interface;
        if (noBody) _bodyEnd = f.EndSpan.End;

        if (!clauses)
        {
            switch (f.Kind)
            {
                case FnKind.Extern: Line($"{sig} from \"{f.ExternTarget}\""); return;
                case FnKind.Spec:
                    Line(sig + " {");
                    SpecBody(f);
                    return;
                default:
                    if (noBody) { Line(sig); return; }
                    Line(sig + " {");
                    Body(f.Body, f.EndSpan.Start);
                    return;
            }
        }
        Line(sig);
        _indent++;
        foreach (var r in f.Requires) Clause("requires", r);
        foreach (var e in f.Ensures) Clause("ensures", e);
        foreach (var t in f.Throws) ThrowsClause(t);
        if (f.Decreases.Count > 0)
        {
            Comments(f.Decreases[0].Span.Start);
            Line("decreases " + string.Join(", ", f.Decreases.Select(d => Expr(d))));
        }
        if (noBody)
        {
            _indent--;
            return;
        }
        if (f.Kind == FnKind.Extern)
        {
            Line($"from \"{f.ExternTarget}\"");
            _indent--;
            return;
        }
        _indent--;
        Line("{");
        if (f.Kind == FnKind.Spec) SpecBody(f);
        else Body(f.Body, f.EndSpan.Start);
    }

    private void SpecBody(FnDecl f)
    {
        _indent++;
        Comments(f.BodyExpr!.Span.Start);
        Line(Expr(f.BodyExpr!));
        _indent--;
        Comments(f.EndSpan.Start);
        Line("}");
    }

    private void Clause(string keyword, Expr e)
    {
        Comments(e.Span.Start);
        Line($"{keyword} {Expr(e)}");
    }

    /// <summary>The statements of a block whose '{' is already written, then the closing '}'.</summary>
    private void Body(List<Stmt> stmts, int end)
    {
        _indent++;
        Stmts(stmts);
        Comments(end);
        _indent--;
        Line("}");
    }

    // ---------- statements ----------

    private void Stmts(List<Stmt> stmts)
    {
        for (var i = 0; i < stmts.Count; i++)
        {
            var s = stmts[i];
            var commentBefore = _nextComment < _comments.Count && _comments[_nextComment].Start < s.Span.Start && !_comments[_nextComment].Trailing;
            Comments(s.Span.Start);
            if (i > 0 && !commentBefore && BlankBefore(s.Span.Line)) Blank();
            Stmt(s);
        }
    }

    private static bool Simple(Stmt s) => s is Let or Set or Return or Assert or Print or Do or Break or Continue or Throw;

    private static bool Compact(List<Stmt> block) => block.Count == 1 && Simple(block[0]);

    /// <summary>The text if it fits on one line at the current indentation, else null.</summary>
    private string? Fits(string text) =>
        2 * _indent + text.Length <= Width && !text.Contains(AlignedLine) ? text : null;

    private string? OneLine(Stmt s)
    {
        if (!Simple(s)) return null;
        return s switch
        {
            Let l => $"{(l.Ghost ? "ghost " : "")}{(l.Mutable ? "var" : "let")} {l.Name}{(l.Annotation != null ? ": " + Type(l.Annotation) : "")} = {Expr(l.Init)}",
            Set st => $"set {st.Name} = {Expr(st.Value)}",
            Return r => $"return {Expr(r.Value)}",
            Assert a => $"assert {Expr(a.Cond)}",
            Print p => $"print {Expr(p.Value)}",
            Do d => $"do {Expr(d.Call)}",
            Throw th => th.Value.Args.Count == 0 ? $"throw {th.Value.Name}" : $"throw {Expr(th.Value)}",
            Break => "break",
            Continue => "continue",
            _ => null,
        };
    }

    private void Stmt(Stmt s)
    {
        if (OneLine(s) is { } text) { Line(text); return; }
        switch (s)
        {
            case If i: IfStmt(i); break;
            case While w:
                Line($"while {Expr(w.Cond)}");
                _indent++;
                foreach (var inv in w.Invariants) Clause("invariant", inv);
                if (w.Decreases.Count > 0) Line("decreases " + string.Join(", ", w.Decreases.Select(d => Expr(d))));
                _indent--;
                if (w.Invariants.Count == 0 && w.Decreases.Count == 0)
                {
                    _out[^1] += " {";
                }
                else Line("{");
                Body(w.Body, s.Span.End);
                break;
            case For fr:
            {
                var vars = fr.Source == null ? fr.Index : fr.Index != null ? $"{fr.Index}, {fr.Elem}" : fr.Elem;
                var range = fr.Source == null ? $"{Expr(fr.Lo!, 4)}..{Expr(fr.Hi!, 4)}" : Expr(fr.Source);
                Line($"for {vars} in {range}");
                _indent++;
                foreach (var inv in fr.Invariants) Clause("invariant", inv);
                _indent--;
                if (fr.Invariants.Count == 0) _out[^1] += " {";
                else Line("{");
                Body(fr.Body, s.Span.End);
                break;
            }
            case MatchStmt m:
                Line($"match {Expr(m.Scrutinee)} {{");
                _indent++;
                foreach (var (p, body) in m.Arms)
                {
                    Comments(p.Span.Start);
                    if (body.Count == 0) Line($"{Pattern(p)} {{ }}");
                    else if (Compact(body) && Fits($"{Pattern(p)} {{ {OneLine(body[0])} }}") is { } arm) Line(arm);
                    else
                    {
                        Line($"{Pattern(p)} {{");
                        Body(body, body.Count > 0 ? body[^1].Span.End : p.Span.End);
                    }
                }
                _indent--;
                Line("}");
                break;
            case Try t:
                Line("try {");
                Body(t.Body, t.Catches[0].Span.Start);
                foreach (var c in t.Catches)
                {
                    var head = c.Binders.Count > 0 ? $"catch {c.Name}({string.Join(", ", c.Binders)})" : $"catch {c.Name}";
                    _out[^1] += $" {head} {{";
                    Body(c.Body, c.Body.Count > 0 ? c.Body[^1].Span.End : c.Span.End);
                }
                break;
        }
    }

    private void IfStmt(If i)
    {
        // Collect the 'else if' chain.
        var branches = new List<(Expr? Cond, List<Stmt> Body)> { (i.Cond, i.Then) };
        var cur = i;
        while (true)
        {
            if (cur.Else == null) break;
            if (cur.Else is [If next]) { branches.Add((next.Cond, next.Then)); cur = next; continue; }
            branches.Add((null, cur.Else));
            break;
        }
        if (branches.All(b => Compact(b.Body)))
        {
            var lines = branches.Select((b, k) =>
                Fits($"{(k == 0 ? $"if {Expr(b.Cond!)}" : b.Cond != null ? $"else if {Expr(b.Cond)}" : "else")} {{ {OneLine(b.Body[0])} }}")).ToList();
            if (lines.All(l => l != null))
            {
                foreach (var l in lines) Line(l!);
                return;
            }
        }
        for (var k = 0; k < branches.Count; k++)
        {
            var (c, body) = branches[k];
            var head = k == 0 ? $"if {Expr(c!)} {{" : c != null ? $"}} else if {Expr(c)} {{" : "} else {";
            if (k == 0) Line(head);
            else _out[^1] = new string(' ', 2 * _indent) + head;
            _indent++;
            Stmts(body);
            var end = k + 1 < branches.Count ? (branches[k + 1].Cond?.Span.Start ?? branches[k + 1].Body.FirstOrDefault()?.Span.Start ?? i.Span.End) : i.Span.End;
            Comments(end);
            _indent--;
            Line("}");
        }
    }

    private string Pattern(Pattern p) =>
        p.Alternatives != null ? string.Join(" | ", p.Alternatives.Select(Pattern))
        : p.Literal != null ? Expr(p.Literal)
        : p.Case == null ? "_" : p.Binders.Count == 0 ? p.Case : $"{p.Case}({string.Join(", ", p.Binders)})";

    private static string Escape(string s) => string.Concat(s.Select(ch => ch switch
    {
        '\\' => "\\\\", '"' => "\\\"", '{' => "\\{", '}' => "\\}", '\n' => "\\n", '\t' => "\\t", '\r' => "\\r", '\0' => "\\0",
        _ => ch.ToString(),
    }));

    // ---------- expressions ----------

    // Precedence, lowest to highest, matching the parser: ==> (0), || (1), && (2), comparison (3), + - (4), * / % (5), unary (6), postfix (7).
    private static int Prec(string op) => op switch
    {
        "==>" => 0,
        "||" => 1,
        "&&" => 2,
        "==" or "!=" or "<" or ">" or "<=" or ">=" => 3,
        "+" or "-" => 4,
        _ => 5,
    };

    private string Expr(Expr e, int ctx = 0)
    {
        string Paren(string s, int prec) => prec < ctx ? $"({s})" : s;
        switch (e)
        {
            case IntLit i: return i.Value.ToString();
            case FloatLit f: return f.Text;
            case DecLit d: return d.Text + "m";
            case StrLit s: return $"\"{Escape(s.Value)}\"";
            case Interp ip: return "\"" + string.Concat(ip.Parts.Select(x => x is StrLit s ? Escape(s.Value) : $"{{{Expr(x)}}}")) + "\"";
            case Lambda l: return $"{(l.Params.Count == 1 ? l.Params[0] : $"({string.Join(", ", l.Params)})")} => {Expr(l.Body)}";
            case WithExpr w: return $"{Expr(w.Target, 7)} with {{ {string.Join(", ", w.Updates.Select(u => $"{u.Field}: {Expr(u.Value)}"))} }}";
            case BoolLit b: return b.Value ? "true" : "false";
            case UnitLit: return "()";
            case Hole h: return "?" + h.Name;
            case Var v: return v.Name;
            case Unary u: return Paren(u.Op + Expr(u.Operand, 6), 6);
            case Binary b:
            {
                var p = Prec(b.Op);
                var (l, r) = b.Op == "==>" ? (1, 0) : p == 3 ? (4, 4) : (p, p + 1);
                var flat = $"{Expr(b.Left, l)} {b.Op} {Expr(b.Right, r)}";
                if (b.Op is not ("&&" or "||") || flat.Length <= CallWidth) return Paren(flat, p);
                // A long chain of one connective puts each operand on its own line, the operator first.
                var operands = new List<string>();
                Expr cur = b;
                while (cur is Binary same && same.Op == b.Op)
                {
                    operands.Insert(0, Expr(same.Right, r));
                    cur = same.Left;
                }
                operands.Insert(0, Expr(cur, l));
                return Paren($"{PushAlign}{string.Join($"{AlignedLine}{b.Op} ", operands)}{PopAlign}", p);
            }
            case IfExpr i: return Paren($"if {Expr(i.Cond)} then {Expr(i.Then)} else {Expr(i.Else)}", ctx > 0 ? int.MinValue : 0);
            case Index ix: return $"{Expr(ix.Array, 7)}[{Expr(ix.At)}]";
            case FieldAccess fa: return $"{Expr(fa.Target, 7)}.{fa.Field}";
            case ArrayLit a:
            {
                var elems = a.Elems.Select(x => Expr(x)).ToList();
                var flat = $"[{string.Join(", ", elems)}]";
                if (elems.Count < 2 || flat.Length <= CallWidth && !flat.Contains(AlignedLine)) return flat;
                return $"[{PushAlign}{string.Join("," + AlignedLine, elems)}]{PopAlign}";
            }
            case TensorLit t: return Tensor(t);
            case MatchExpr m:
            {
                var arms = m.Arms.Select(a => $"{Pattern(a.Pattern)} => {Expr(a.Body)}").ToList();
                return $"match {Expr(m.Scrutinee)} {{ {string.Join(", ", arms)} }}";
            }
            case Quant q: return Paren(Quant(q), ctx > 0 ? int.MinValue : 0);
            case Call c:
            {
                var shape = c.ShapeArg != null ? Type(c.ShapeArg)["Tensor".Length..] : "";
                var args = c.Args.Select((a, k) => c.ArgNames[k] is { } n ? $"{n}: {Expr(a)}" : Expr(a)).ToList();
                var callee = c.Name;
                var prefix = c.Awaited ? "await " : "";
                if (c.Method)
                {
                    callee = $"{Expr(c.Args[0], 7)}.{c.Name}";
                    args.RemoveAt(0);
                }
                var flat = $"{prefix}{callee}{shape}({string.Join(", ", args)})";
                if (args.Count < 2 || flat.Length <= CallWidth && !flat.Contains(AlignedLine)) return flat;
                return $"{prefix}{callee}{shape}({PushAlign}{string.Join("," + AlignedLine, args)}){PopAlign}";
            }
        }
        throw new InvalidOperationException($"cannot format {e.GetType().Name}");
    }

    private string Quant(Quant q)
    {
        var kw = q.ForAll ? "forall" : "exists";
        switch (q.Kind)
        {
            case QuantKind.Range:
                return $"{kw} {q.Binders[0].Name} in {Expr(q.Lo!, 4)}..{Expr(q.Hi!, 4)} : {Expr(q.Body)}";
            case QuantKind.Elems:
                return $"{kw} {q.Binders[0].Name} in elems({Expr(q.Source!)}) : {Expr(q.Body)}";
            default:
                var binders = string.Join(", ", q.Binders.Select(b => $"{b.Name}: {Type(b.Type)}"));
                var triggers = string.Concat(q.Triggers.Select(t => " trigger " + string.Join(", ", t.Select(x => Expr(x, 6)))));
                return $"{kw} {binders}{triggers} : {Expr(q.Body)}";
        }
    }

    /// <summary>A tensor literal; a matrix or higher puts one row of the last dimension per line, aligned under the first value.</summary>
    private string Tensor(TensorLit t)
    {
        var head = $"tensor[{(t.Elem == ElemType.Float64 ? "Float64; " : "")}{string.Join(", ", t.Shape)}](";
        if (t.Shape.Count < 2 || t.Shape[^1] <= 0) return head + string.Join(", ", t.Texts) + ")";
        var row = (int)t.Shape[^1];
        if (row == 1) return head + string.Join(", ", t.Texts) + ")";
        var rows = t.Texts.Chunk(row).Select(r => string.Join(", ", r));
        return head + PushAlign + string.Join("," + AlignedLine, rows) + ")" + PopAlign;
    }
}
