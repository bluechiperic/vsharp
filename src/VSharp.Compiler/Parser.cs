using System.Globalization;

namespace VSharp.Compiler;

public enum Tok { Ident, Kw, Int, Float, Dec, Str, Sym, Eof }

public readonly record struct Token(Tok Kind, string Text, int Start, int End, int Line, int Col, int File = 0)
{
    public Span Span => new(Start, End, Line, Col, Line, Col + (End - Start), File);
}

public static class Lexer
{
    public static readonly HashSet<string> Keywords =
    [
        "module", "fn", "requires", "ensures", "decreases", "effects", "let", "var", "set", "if", "then", "else",
        "while", "invariant", "return", "assert", "print", "do", "true", "false", "forall", "exists", "in",
        "result", "tensor", "type", "where", "self", "match", "ghost", "spec", "lemma", "extern",
        "for", "break", "continue", "with", "const",
    ];

    private static readonly string[] Symbols =
    [
        "==>", "==", "=>", "!=", "<=", ">=", "->", "&&", "||", "..",
        "(", ")", "{", "}", "[", "]", ",", ":", ";", "=", "<", ">", "+", "-", "*", "/", "%", "!", ".", "?", "|", "@",
    ];

    public static List<Token> Lex(string src, int file = 0) => Lex(src, out _, file);

    /// <summary>
    /// Tokenizes <paramref name="src"/>. For text embedded in a string literal, <paramref name="baseOffset"/> and
    /// <paramref name="baseLine"/>/<paramref name="baseCol"/> place the tokens at their position in the file.
    /// </summary>
    public static List<Token> Lex(string src, out List<Comment> comments, int file = 0, int baseOffset = 0, int baseLine = 1, int baseCol = 1)
    {
        comments = [];
        var toks = new List<Token>();
        int i = 0, line = baseLine, lineStart = -(baseCol - 1);
        var lastTokenLine = 0;
        Span At(int s, int e, int col) => new(baseOffset + s, baseOffset + e, line, col, line, col + (e - s), file);
        while (i < src.Length)
        {
            var c = src[i];
            if (c == '\n') { i++; line++; lineStart = i; continue; }
            if (char.IsWhiteSpace(c)) { i++; continue; }
            if (c == '/' && i + 1 < src.Length && src[i + 1] == '/')
            {
                var s = i;
                while (i < src.Length && src[i] != '\n') i++;
                comments.Add(new Comment(baseOffset + s, line, src[s..i].TrimEnd('\r'), lastTokenLine == line));
                continue;
            }
            var start = i;
            var col = i - lineStart + 1;
            lastTokenLine = line;
            void Add(Tok kind, string text) => toks.Add(new Token(kind, text, baseOffset + start, baseOffset + i, line, col, file));
            if (char.IsAsciiLetter(c) || c == '_')
            {
                while (i < src.Length && (char.IsAsciiLetterOrDigit(src[i]) || src[i] == '_')) i++;
                var text = src[start..i];
                Add(Keywords.Contains(text) ? Tok.Kw : Tok.Ident, text);
                continue;
            }
            if (char.IsAsciiDigit(c))
            {
                while (i < src.Length && char.IsAsciiDigit(src[i])) i++;
                var kind = Tok.Int;
                // "0..n" is a range, "0.5" is a float: only consume '.' when a digit follows.
                if (i + 1 < src.Length && src[i] == '.' && char.IsAsciiDigit(src[i + 1]))
                {
                    i++;
                    while (i < src.Length && char.IsAsciiDigit(src[i])) i++;
                    kind = Tok.Float;
                }
                // A trailing 'm' makes a Decimal literal, as in C#: 12.50m, 3m.
                if (i < src.Length && src[i] == 'm' && (i + 1 >= src.Length || !(char.IsAsciiLetterOrDigit(src[i + 1]) || src[i + 1] == '_')))
                {
                    i++;
                    Add(Tok.Dec, src[start..(i - 1)]);
                    continue;
                }
                Add(kind, src[start..i]);
                continue;
            }
            if (c == '"')
            {
                i++;
                while (i < src.Length && src[i] != '"' && src[i] != '\n') i += src[i] == '\\' && i + 1 < src.Length && src[i + 1] != '\n' ? 2 : 1;
                if (i >= src.Length || src[i] != '"')
                    throw new CompileError("TN1001", At(start, i, col), "unterminated string literal", "A string literal ends on the line it starts; write a newline as \\n.");
                i++;
                toks.Add(new Token(Tok.Str, src[(start + 1)..(i - 1)], baseOffset + start, baseOffset + i, line, col, file));
                continue;
            }
            var sym = Symbols.FirstOrDefault(s => string.CompareOrdinal(src, i, s, 0, s.Length) == 0);
            if (sym == null)
                throw new CompileError("TN1001", At(start, start + 1, col), $"unexpected character '{c}'");
            i += sym.Length;
            Add(Tok.Sym, sym);
        }
        toks.Add(new Token(Tok.Eof, "<end of file>", baseOffset + src.Length, baseOffset + src.Length, line, src.Length - lineStart + 1, file));
        return toks;
    }
}

public sealed class Parser(List<Token> toks)
{
    private int _p;

    private Token Cur => toks[_p];
    private Token Peek(int k = 1) => toks[Math.Min(_p + k, toks.Count - 1)];
    private Token Prev => toks[_p - 1];
    private bool IsSym(string s) => Cur.Kind == Tok.Sym && Cur.Text == s;
    private bool IsKw(string s) => Cur.Kind == Tok.Kw && Cur.Text == s;
    private Token Next() => toks[_p++];
    private bool TrySym(string s) { if (!IsSym(s)) return false; _p++; return true; }
    private bool TryKw(string s) { if (!IsKw(s)) return false; _p++; return true; }

    private CompileError Fail(string message, string? hint = null) => new("TN1001", Cur.Span, message, hint);

    private void Sym(string s) { if (!TrySym(s)) throw Fail($"expected '{s}' but found '{Cur.Text}'"); }
    private void Kw(string s) { if (!TryKw(s)) throw Fail($"expected '{s}' but found '{Cur.Text}'"); }

    // Contextual keywords: reserved only where they can appear, so they stay usable as names ('grad' especially).
    private bool TryWord(string s) { if (Cur.Kind != Tok.Ident || Cur.Text != s) return false; _p++; return true; }
    private void Word(string s) { if (!TryWord(s)) throw Fail($"expected '{s}' but found '{Cur.Text}'"); }

    private Token Ident(string what)
    {
        if (Cur.Kind != Tok.Ident) throw Fail($"expected {what} but found '{Cur.Text}'");
        return Next();
    }

    private Span From(Token start) => new(start.Start, Prev.End, start.Line, start.Col, Prev.Line, Prev.Col + (Prev.End - Prev.Start), start.File);

    private T At<T>(Token start, T e) where T : Expr { e.Span = From(start); return e; }

    public ModuleDecl ParseModule()
    {
        Kw("module");
        var name = Ident("a module name");
        var module = new ModuleDecl { Name = name.Text, NameSpan = name.Span };
        if (TryWord("total")) module.TotalByDefault = true;
        ParseDecls(module);
        return module;
    }

    /// <summary>Parses declarations until end of file (also used for the prelude, which has no module header).</summary>
    public void ParseDecls(ModuleDecl module)
    {
        while (Cur.Kind != Tok.Eof)
        {
            var start = Cur;
            if (Cur.Kind == Tok.Ident && Cur.Text == "use" && Peek().Kind == Tok.Ident)
            {
                Next();
                var ns = Cur;
                module.Uses.Add((DottedName("a namespace"), From(ns), start.Start));
                continue;
            }
            var attrs = ParseAttrs();
            if (IsKw("type")) module.Types.Add(ParseType(attrs, start));
            else if (IsKw("fn") || IsKw("spec") || IsKw("lemma") || IsKw("extern")) module.Fns.Add(ParseFn(attrs, start));
            else if (IsKw("const"))
            {
                if (attrs.Count > 0) throw new CompileError("TN2026", attrs[0].Span, "a constant cannot have attributes", "Constants are inlined where they are used, so they have no .NET form.");
                module.Consts.Add(ParseConst());
            }
            else if (TryWord("class")) module.Types.Add(ParseClass(attrs, start));
            else if (TryWord("interface")) module.Types.Add(ParseInterface(attrs, start));
            else if (Cur.Kind == Tok.Ident && Cur.Text == "exception" && Peek().Kind == Tok.Ident)
            {
                Next();
                module.Exceptions.Add(ParseException(attrs, start));
            }
            else throw Fail($"expected a declaration but found '{Cur.Text}'",
                "A module contains 'use', 'type', 'class', 'interface', 'exception', 'const', 'fn', 'spec fn', 'lemma fn' and 'extern fn' declarations.");
        }
    }

    /// <summary>'A.B.C': a name with dots, for namespaces and .NET types.</summary>
    private string DottedName(string what)
    {
        var name = Ident(what).Text;
        while (IsSym(".") && Peek().Kind == Tok.Ident)
        {
            Next();
            name += "." + Next().Text;
        }
        return name;
    }

    /// <summary>Zero or more '@Name' or '@Name(args)' attributes.</summary>
    private List<Attr> ParseAttrs()
    {
        var attrs = new List<Attr>();
        while (IsSym("@"))
        {
            var start = Next();
            var name = DottedName("an attribute name");
            var parens = IsSym("(");
            var (args, names) = parens ? ParseArgs() : ([], []);
            attrs.Add(new Attr { Name = name, Span = From(start), Args = args, ArgNames = names, HasParens = parens });
        }
        return attrs;
    }

    /// <summary>'(' args ')' of a call: each argument optionally named, lambdas allowed.</summary>
    private (List<Expr> Args, List<string?> Names) ParseArgs()
    {
        Sym("(");
        var args = new List<Expr>();
        var names = new List<string?>();
        if (!IsSym(")"))
        {
            do
            {
                string? argName = null;
                if (Cur.Kind == Tok.Ident && Peek().Kind == Tok.Sym && Peek().Text == ":")
                {
                    argName = Next().Text;
                    Next();
                }
                names.Add(argName);
                args.Add(AtLambda() ? ParseLambda() : ParseExpr());
            } while (TrySym(","));
        }
        Sym(")");
        return (args, names);
    }

    private TypeDecl ParseClass(List<Attr> attrs, Token start)
    {
        var name = Ident("a class name");
        if (IsSym("[")) throw Fail("a class cannot be generic", "Use a generic record (type Box[T] = { value: T }) with module functions.");
        var decl = new TypeDecl { Name = name.Text, NameSpan = name.Span, Kind = TypeKind.Record, IsClass = true, Start = start.Start, Attrs = attrs };
        Sym("(");
        if (!IsSym(")")) do decl.Fields.Add(ParseField()); while (TrySym(","));
        Sym(")");
        if (TryWord("implements"))
        {
            do
            {
                var i = Ident("an interface name");
                decl.ImplementsNames.Add((i.Text, i.Span));
            } while (TrySym(","));
        }
        Sym("{");
        while (!IsSym("}"))
        {
            var member = Cur;
            if (TryKw("invariant"))
            {
                if (decl.Methods.Count > 0) throw new CompileError("TN1001", member.Span, "a class's invariants come before its methods");
                decl.Invariants.Add(ParseExpr());
                continue;
            }
            var mattrs = ParseAttrs();
            if (!IsKw("fn") && !IsKw("spec"))
                throw Fail($"expected 'invariant', 'fn' or 'spec fn' in class '{name.Text}' but found '{Cur.Text}'",
                    "A class contains invariants, then methods. Methods take 'self' as their first parameter.");
            decl.Methods.Add(ParseFn(mattrs, member, decl));
        }
        Sym("}");
        decl.EndSpan = Prev.Span;
        return decl;
    }

    private TypeDecl ParseInterface(List<Attr> attrs, Token start)
    {
        var name = Ident("an interface name");
        if (IsSym("[")) throw Fail("an interface cannot be generic");
        var decl = new TypeDecl { Name = name.Text, NameSpan = name.Span, Kind = TypeKind.Interface, Start = start.Start, Attrs = attrs };
        Sym("{");
        while (!IsSym("}"))
        {
            var member = Cur;
            var mattrs = ParseAttrs();
            if (!IsKw("fn"))
                throw Fail($"expected 'fn' in interface '{name.Text}' but found '{Cur.Text}'",
                    "An interface lists method signatures with their contracts: fn name(self, ...) -> T requires ... ensures ...");
            decl.Methods.Add(ParseFn(mattrs, member, decl));
        }
        Sym("}");
        decl.EndSpan = Prev.Span;
        return decl;
    }

    private ExceptionDecl ParseException(List<Attr> attrs, Token start)
    {
        var name = Ident("an exception name");
        if (TryWord("from"))
        {
            if (Cur.Kind != Tok.Str) throw Fail("expected a string naming a .NET exception type, such as \"System.FormatException\"");
            return new ExceptionDecl { Name = name.Text, NameSpan = name.Span, Start = start.Start, Attrs = attrs, ClrName = Next().Text };
        }
        var decl = new ExceptionDecl { Name = name.Text, NameSpan = name.Span, Start = start.Start, Attrs = attrs };
        if (TrySym("("))
        {
            if (!IsSym(")")) do decl.Fields.Add(ParseField()); while (TrySym(","));
            Sym(")");
        }
        return decl;
    }

    private ConstDecl ParseConst()
    {
        var start = Cur;
        Kw("const");
        var name = Ident("a constant name");
        Sym(":");
        var type = ParseTypeRef();
        Sym("=");
        return new ConstDecl { Name = name.Text, NameSpan = name.Span, Type = type, Value = ParseExpr(), Start = start.Start };
    }

    // ---------- declarations ----------

    private TypeDecl ParseType(List<Attr> attrs, Token start)
    {
        Kw("type");
        var name = Ident("a type name");
        var typeParams = new List<string>();
        if (TrySym("["))
        {
            do typeParams.Add(Ident("a type parameter").Text); while (TrySym(","));
            Sym("]");
        }
        Sym("=");
        TypeDecl decl;
        if (TrySym("{"))
        {
            decl = new TypeDecl { Name = name.Text, NameSpan = name.Span, Kind = TypeKind.Record, Start = start.Start, Attrs = attrs };
            if (!IsSym("}")) do decl.Fields.Add(ParseField()); while (TrySym(","));
            Sym("}");
        }
        else if (IsSym("|"))
        {
            decl = new TypeDecl { Name = name.Text, NameSpan = name.Span, Kind = TypeKind.Union, Start = start.Start, Attrs = attrs };
            while (TrySym("|"))
            {
                var c = Ident("a case name");
                var cd = new CaseDecl { Name = c.Text, Span = c.Span };
                if (TrySym("("))
                {
                    if (!IsSym(")")) do cd.Fields.Add(ParseField()); while (TrySym(","));
                    Sym(")");
                }
                decl.Cases.Add(cd);
            }
        }
        else
        {
            decl = new TypeDecl { Name = name.Text, NameSpan = name.Span, Kind = TypeKind.Refinement, Start = start.Start, Base = ParseTypeRef(), Attrs = attrs };
            Kw("where");
            decl.Pred = ParseExpr();
        }
        decl.TypeParams.AddRange(typeParams);
        return decl;
    }

    private FieldDecl ParseField()
    {
        var attrs = ParseAttrs();
        var f = Ident("a field name");
        Sym(":");
        return new FieldDecl(f.Text, ParseTypeRef(), f.Span) { Attrs = attrs };
    }

    /// <summary>A function, or a method of <paramref name="owner"/> (without a body when the owner is an interface).</summary>
    private FnDecl ParseFn(List<Attr> attrs, Token start, TypeDecl? owner = null)
    {
        var kind = FnKind.Fn;
        if (TryKw("spec")) kind = FnKind.Spec;
        else if (TryKw("lemma")) kind = FnKind.Lemma;
        else if (TryKw("extern")) kind = FnKind.Extern;
        Kw("fn");
        var name = Ident(owner == null ? "a function name" : "a method name");
        var fn = new FnDecl
        {
            Name = owner == null ? name.Text : $"{owner.Name}.{name.Text}", Member = owner == null ? null : name.Text,
            NameSpan = name.Span, Kind = kind, Start = start.Start, Attrs = attrs, Owner = owner,
        };

        if (kind == FnKind.Fn && owner == null && TrySym("="))
        {
            Word("grad");
            fn.Kind = FnKind.Grad;
            fn.GradOf = Ident("the function to differentiate").Text;
            Word("wrt");
            fn.GradWrt = Ident("a parameter name").Text;
            fn.EndSpan = Prev.Span;
            return fn;
        }

        if (TrySym("["))
        {
            do fn.Generics.Add(Ident("a type or dimension parameter").Text); while (TrySym(","));
            Sym("]");
        }
        Sym("(");
        var more = !IsSym(")");
        if (owner != null)
        {
            if (!IsKw("self")) throw Fail($"a method's first parameter is 'self' but found '{Cur.Text}'", $"Write fn {name.Text}(self, ...). Use a module function for code that needs no '{owner.Name}'.");
            var self = Next();
            fn.Params.Add(new Param("self", TType.Unresolved(owner.Name, [], self.Span), self.Span));
            more = TrySym(",");
        }
        if (more)
        {
            do
            {
                var pattrs = ParseAttrs();
                var p = Ident("a parameter name");
                Sym(":");
                fn.Params.Add(new Param(p.Text, ParseTypeRef(), p.Span) { Attrs = pattrs });
            } while (TrySym(","));
        }
        Sym(")");
        if (kind == FnKind.Lemma) { if (TrySym("->")) fn.Ret = ParseTypeRef(); }
        else { Sym("->"); fn.Ret = ParseTypeRef(); }

        while (true)
        {
            if (TryKw("requires")) fn.Requires.Add(ParseExpr());
            else if (TryKw("ensures")) fn.Ensures.Add(ParseExpr());
            else if (IsKw("decreases"))
            {
                if (fn.Decreases.Count > 0) throw Fail("a function has at most one 'decreases' clause", "Use 'decreases a, b' for a lexicographic measure.");
                Next();
                do fn.Decreases.Add(ParseExpr()); while (TrySym(","));
            }
            else if (TryKw("effects"))
            {
                do
                {
                    var e = Ident("an effect name");
                    if (e.Text is not ("io" or "device" or "async"))
                        throw new CompileError("TN1001", e.Span, $"unknown effect '{e.Text}'", "The effects are 'io', 'device' and 'async'.");
                    fn.Effects.Add(e.Text);
                } while (TrySym(","));
            }
            else if (TryWord("total")) fn.Total = true;
            else if (Cur.Kind == Tok.Ident && Cur.Text == "throws" && Peek().Kind == Tok.Ident)
            {
                var at = Next();
                var exc = Ident("an exception name");
                var when = TryWord("when") ? ParseExpr() : null;
                fn.Throws.Add(new ThrowsClause { Name = exc.Text, Span = From(at), When = when });
            }
            else break;
        }

        if (owner?.Kind == TypeKind.Interface)
        {
            if (IsSym("{")) throw Fail("an interface method has no body", "Each class that implements the interface provides the body.");
            fn.EndSpan = Prev.Span;
            return fn;
        }
        if (owner != null && kind is FnKind.Lemma or FnKind.Extern)
            throw new CompileError("TN1001", start.Span, "a class contains 'fn' and 'spec fn' methods only", "Declare lemmas and extern functions at module level.");
        switch (kind)
        {
            case FnKind.Extern:
                Word("from");
                if (Cur.Kind != Tok.Str) throw Fail("expected a string naming a .NET method, such as \"System.Math.Sqrt\"");
                fn.ExternTarget = Next().Text;
                break;
            case FnKind.Spec:
                Sym("{");
                fn.BodyExpr = ParseExpr();
                Sym("}");
                break;
            default:
                fn.Body = ParseBlock();
                break;
        }
        fn.EndSpan = Prev.Span;
        return fn;
    }

    // ---------- types ----------

    public TType ParseTypeRef()
    {
        var t = Ident("a type");
        switch (t.Text)
        {
            case "Int": return TType.Int;
            case "Bool": return TType.Bool;
            case "Unit": return TType.Unit;
            case "Float": return TType.Float;
            case "String": return TType.String;
            case "Date": return TType.Date;
            case "Decimal": return TType.Decimal;
            case "Int32": return TType.Int32;
            case "Array":
                Sym("[");
                var elem = ParseTypeRef();
                Sym("]");
                return TType.ArrayOf(elem);
            case "Set":
                Sym("[");
                var item = ParseTypeRef();
                Sym("]");
                return TType.SetOf(item);
            case "Map":
                Sym("[");
                var key = ParseTypeRef();
                Sym(",");
                var value = ParseTypeRef();
                Sym("]");
                return TType.MapOf(key, value);
            case "Tensor":
                Sym("[");
                var shape = ParseShape(t);
                Sym("]");
                return shape;
            default:
                var args = new List<TType>();
                if (TrySym("["))
                {
                    do args.Add(ParseTypeRef()); while (TrySym(","));
                    Sym("]");
                }
                return TType.Unresolved(t.Text, args, From(t));
        }
    }

    /// <summary>Parses '[Float64;] d1, d2, ...' up to (not including) the closing bracket.</summary>
    private TType ParseShape(Token at)
    {
        var elem = ElemType.Float32;
        if (Cur.Kind == Tok.Ident && Cur.Text is "Float32" or "Float64" && Peek().Text == ";")
        {
            elem = Next().Text == "Float64" ? ElemType.Float64 : ElemType.Float32;
            Sym(";");
        }
        var dims = new List<Dim>();
        if (!IsSym("]")) do dims.Add(ParseDim()); while (TrySym(","));
        return TType.Tensor(elem, dims);
    }

    private Dim ParseDim()
    {
        var d = ParseDimTerm();
        while (TrySym("+")) d = Dim.Bin('+', d, ParseDimTerm());
        return d;
    }

    private Dim ParseDimTerm()
    {
        var d = ParseDimAtom();
        while (TrySym("*")) d = Dim.Bin('*', d, ParseDimAtom());
        return d;
    }

    private Dim ParseDimAtom()
    {
        if (Cur.Kind == Tok.Int) return Dim.Of(ParseLong(Next()));
        if (TrySym("("))
        {
            var d = ParseDim();
            Sym(")");
            return d;
        }
        if (Cur.Kind == Tok.Ident) return Dim.Var(Next().Text);
        throw Fail($"expected a dimension but found '{Cur.Text}'", "Dimensions are positive integers, dimension parameters, or sums and products of them.");
    }

    private static long ParseLong(Token t) =>
        long.TryParse(t.Text, NumberStyles.None, CultureInfo.InvariantCulture, out var v)
            ? v
            : throw new CompileError("TN1001", t.Span, $"integer literal '{t.Text}' does not fit in Int (64-bit)");

    // ---------- statements ----------

    private List<Stmt> ParseBlock()
    {
        Sym("{");
        var stmts = new List<Stmt>();
        while (!IsSym("}")) stmts.Add(ParseStmt());
        Sym("}");
        return stmts;
    }

    private Stmt ParseStmt()
    {
        var start = Cur;
        var s = ParseStmtCore();
        s.Span = From(start);
        return s;
    }

    private Stmt ParseStmtCore()
    {
        var ghost = TryKw("ghost");
        if (ghost && !IsKw("let") && !IsKw("var")) throw Fail("'ghost' must be followed by 'let' or 'var'");
        if (IsKw("let") || IsKw("var"))
        {
            var mutable = Next().Text == "var";
            var name = Ident("a variable name").Text;
            var ann = TrySym(":") ? ParseTypeRef() : null;
            Sym("=");
            return new Let(name, mutable, ann, ParseValue()) { Ghost = ghost };
        }
        if (TryKw("set"))
        {
            var name = Ident("a variable name").Text;
            Sym("=");
            return new Set(name, ParseValue());
        }
        if (IsKw("if")) return ParseIf();
        if (TryKw("while"))
        {
            var cond = ParseExpr();
            var invs = new List<Expr>();
            var dec = new List<Expr>();
            while (true)
            {
                if (TryKw("invariant")) invs.Add(ParseExpr());
                else if (IsKw("decreases"))
                {
                    if (dec.Count > 0) throw Fail("a loop has at most one 'decreases' clause", "Use 'decreases a, b' for a lexicographic measure.");
                    Next();
                    do dec.Add(ParseExpr()); while (TrySym(","));
                }
                else break;
            }
            return new While(cond, invs, dec, ParseBlock());
        }
        if (TryKw("for")) return ParseFor();
        if (TryKw("break")) return new Break();
        if (TryKw("continue")) return new Continue();
        if (TryKw("match"))
        {
            var scrutinee = ParseExpr();
            Sym("{");
            var arms = new List<(Pattern, List<Stmt>)>();
            while (!IsSym("}")) arms.Add((ParsePattern(), ParseBlock()));
            Sym("}");
            return new MatchStmt(scrutinee, arms);
        }
        if (TryKw("return")) return new Return(ParseValue());
        if (TryKw("assert")) return new Assert(ParseExpr());
        if (TryKw("print")) return new Print(ParseExpr());
        if (TryKw("do")) return new Do(ParseValue());
        if (Cur.Kind == Tok.Ident && Cur.Text == "throw" && Peek().Kind == Tok.Ident)
        {
            var at = Next();
            var e = ParseExpr();
            if (e is Var v) e = new Call(v.Name, [], []) { Span = v.Span };
            if (e is not Call { Method: false } c)
                throw new CompileError("TN2030", at.Span, "'throw' must be followed by an exception", "Write: throw Overdrawn(needed: amount)");
            return new Throw(c);
        }
        if (Cur.Kind == Tok.Ident && Cur.Text == "try" && Peek().Kind == Tok.Sym && Peek().Text == "{")
        {
            Next();
            var body = ParseBlock();
            var catches = new List<Catch>();
            while (Cur.Kind == Tok.Ident && Cur.Text == "catch")
            {
                var at = Next();
                var exc = Ident("an exception name");
                var binders = new List<string>();
                if (TrySym("("))
                {
                    if (!IsSym(")")) do binders.Add(Ident("a name for a field of the exception, or '_'").Text); while (TrySym(","));
                    Sym(")");
                }
                catches.Add(new Catch { Name = exc.Text, Span = From(at), Binders = binders, Body = ParseBlock() });
            }
            if (catches.Count == 0) throw Fail("'try' needs at least one 'catch'", "Write: try { ... } catch Overdrawn(needed) { ... }");
            return new Try(body, catches);
        }
        throw Fail($"expected a statement but found '{Cur.Text}'",
            "Every statement starts with a keyword: let, var, ghost, set, if, while, for, break, continue, match, return, assert, print, do, throw, try.");
    }

    /// <summary>The value of a let, var, set, return or do statement: an expression, or 'await' and a call.</summary>
    private Expr ParseValue()
    {
        if (Cur.Kind != Tok.Ident || Cur.Text != "await" || Peek().Kind != Tok.Ident) return ParseExpr();
        var at = Next();
        var e = ParseExpr();
        if (e is not Call c)
            throw new CompileError("TN2029", at.Span, "'await' must be followed by a call to an async function", "Write: let x = await f(...)");
        c.Awaited = true;
        return c;
    }

    private For ParseFor()
    {
        var first = Ident("a loop variable name").Text;
        string? second = TrySym(",") ? Ident("an element variable name").Text : null;
        Kw("in");
        var from = ParseAdd();
        var invariants = new List<Expr>();
        void Clauses()
        {
            while (true)
            {
                if (TryKw("invariant")) invariants.Add(ParseExpr());
                else if (IsKw("decreases")) throw Fail("a 'for' loop needs no 'decreases' clause", "A 'for' loop always terminates: its index counts up to a fixed bound.");
                else break;
            }
        }
        if (TrySym(".."))
        {
            if (second != null) throw Fail("'for i, x in' iterates an array, not a range", "Write 'for i in lo..hi' to count, or 'for i, x in items' to iterate an array with its index.");
            var hi = ParseAdd();
            Clauses();
            return new For { Index = first, Lo = from, Hi = hi, Invariants = invariants, Body = ParseBlock() };
        }
        Clauses();
        return second == null
            ? new For { Elem = first, Source = from, Invariants = invariants, Body = ParseBlock() }
            : new For { Index = first, Elem = second, Source = from, Invariants = invariants, Body = ParseBlock() };
    }

    private If ParseIf()
    {
        var start = Cur;
        Kw("if");
        var cond = ParseExpr();
        if (IsKw("then")) throw Fail("'if ... then ... else' is an expression, not a statement", "Use 'if cond { ... } else { ... }' for statements.");
        var then = ParseBlock();
        List<Stmt>? els = null;
        if (TryKw("else")) els = IsKw("if") ? [ParseIf()] : ParseBlock();
        return new If(cond, then, els) { Span = From(start) };
    }

    private Pattern ParsePattern()
    {
        var start = Cur;
        var first = ParsePatternAlt();
        if (!IsSym("|")) return first;
        var alts = new List<Pattern> { first };
        while (TrySym("|")) alts.Add(ParsePatternAlt());
        return new Pattern { Alternatives = alts, Span = From(start) };
    }

    private Pattern ParsePatternAlt()
    {
        var start = Cur;
        if (Cur.Kind is Tok.Int or Tok.Dec or Tok.Str || IsKw("true") || IsKw("false") || IsSym("-") && Peek().Kind is Tok.Int or Tok.Dec)
            return new Pattern { Literal = ParseUnary(), Span = From(start) };
        var name = Ident("a case name, a literal or '_'");
        if (name.Text == "_") return new Pattern { Case = null, Span = name.Span };
        var binders = new List<string>();
        if (TrySym("("))
        {
            if (!IsSym(")")) do binders.Add(Ident("a binder name or '_'").Text); while (TrySym(","));
            Sym(")");
        }
        return new Pattern { Case = name.Text, Binders = binders, Span = From(start) };
    }

    // ---------- expressions ----------

    // Precedence, lowest to highest: ==>  ||  &&  comparison  + -  * / %  unary  postfix
    public Expr ParseExpr()
    {
        var start = Cur;
        var left = ParseOr();
        return TrySym("==>") ? At(start, new Binary("==>", left, ParseExpr())) : left;
    }

    private Expr ParseOr()
    {
        var start = Cur;
        var left = ParseAnd();
        while (TrySym("||")) left = At(start, new Binary("||", left, ParseAnd()));
        return left;
    }

    private Expr ParseAnd()
    {
        var start = Cur;
        var left = ParseCmp();
        while (TrySym("&&")) left = At(start, new Binary("&&", left, ParseCmp()));
        return left;
    }

    private static readonly string[] CmpOps = ["==", "!=", "<=", ">=", "<", ">"];

    private Expr ParseCmp()
    {
        var start = Cur;
        var left = ParseAdd();
        if (Cur.Kind != Tok.Sym || !CmpOps.Contains(Cur.Text)) return left;
        var op = Next().Text;
        var e = At(start, new Binary(op, left, ParseAdd()));
        if (Cur.Kind == Tok.Sym && CmpOps.Contains(Cur.Text))
            throw Fail("comparisons cannot be chained", "Write 'a <= b && b <= c' instead of 'a <= b <= c'.");
        return e;
    }

    private Expr ParseAdd()
    {
        var start = Cur;
        var left = ParseMul();
        while (IsSym("+") || IsSym("-")) { var op = Next().Text; left = At(start, new Binary(op, left, ParseMul())); }
        return left;
    }

    private Expr ParseMul()
    {
        var start = Cur;
        var left = ParseUnary();
        while (IsSym("*") || IsSym("/") || IsSym("%")) { var op = Next().Text; left = At(start, new Binary(op, left, ParseUnary())); }
        return left;
    }

    private Expr ParseUnary()
    {
        var start = Cur;
        if (TrySym("-")) return At(start, new Unary("-", ParseUnary()));
        if (TrySym("!")) return At(start, new Unary("!", ParseUnary()));
        var e = ParsePrimary();
        while (true)
        {
            if (TrySym("["))
            {
                var at = ParseExpr();
                Sym("]");
                e = At(start, new Index(e, at));
            }
            else if (TrySym("."))
            {
                var member = Ident("a field or method name").Text;
                if (IsSym("("))
                {
                    var (args, names) = ParseArgs();
                    args.Insert(0, e);
                    names.Insert(0, null);
                    e = At(start, new Call(member, args, names) { Method = true });
                }
                else e = At(start, new FieldAccess(e, member));
            }
            else if (TryKw("with"))
            {
                Sym("{");
                var updates = new List<(string, Expr)>();
                do
                {
                    var f = Ident("a field name").Text;
                    Sym(":");
                    updates.Add((f, ParseExpr()));
                } while (TrySym(","));
                Sym("}");
                e = At(start, new WithExpr(e, updates));
            }
            else return e;
        }
    }

    /// <summary>Splits a string literal's text into literal parts and '{expr}' parts, decoding escapes.</summary>
    private Expr ParseString(Token tok)
    {
        var raw = tok.Text;
        var parts = new List<Expr>();
        var sb = new System.Text.StringBuilder();
        var interpolated = false;
        // Offset of raw[k] in the file is tok.Start + 1 + k (string literals do not span lines).
        Span SpanAt(int a, int b) => new(tok.Start + 1 + a, tok.Start + 1 + b, tok.Line, tok.Col + 1 + a, tok.Line, tok.Col + 1 + b, tok.File);
        void Flush()
        {
            if (sb.Length == 0) return;
            parts.Add(new StrLit(sb.ToString()) { Span = tok.Span });
            sb.Clear();
        }
        for (var k = 0; k < raw.Length; k++)
        {
            var c = raw[k];
            if (c == '\\')
            {
                var e = raw[++k];
                sb.Append(e switch
                {
                    'n' => '\n', 't' => '\t', 'r' => '\r', '0' => '\0', '\\' => '\\', '"' => '"', '{' => '{', '}' => '}',
                    _ => throw new CompileError("TN1001", SpanAt(k - 1, k + 1), $"unknown escape '\\{e}'", "The escapes are \\n \\t \\r \\0 \\\\ \\\" \\{ and \\}."),
                });
                continue;
            }
            if (c == '}') throw new CompileError("TN1001", SpanAt(k, k + 1), "unmatched '}' in a string literal", "Write a literal brace as \\}.");
            if (c != '{') { sb.Append(c); continue; }
            var close = raw.IndexOf('}', k + 1);
            if (close < 0) throw new CompileError("TN1001", SpanAt(k, k + 1), "unterminated '{' in a string literal", "Write a literal brace as \\{.");
            var inner = raw[(k + 1)..close];
            if (inner.Contains('"') || inner.Contains('{'))
                throw new CompileError("TN1001", SpanAt(k, close + 1), "an interpolated expression cannot contain strings or braces", "Bind the value with 'let' first and interpolate the variable.");
            if (string.IsNullOrWhiteSpace(inner)) throw new CompileError("TN1001", SpanAt(k, close + 1), "empty interpolation '{}'", "Write a literal brace as \\{.");
            Flush();
            var sub = new Parser(Lexer.Lex(inner, out _, tok.File, tok.Start + 2 + k, tok.Line, tok.Col + 2 + k));
            var expr = sub.ParseExpr();
            if (sub.Cur.Kind != Tok.Eof) throw new CompileError("TN1001", sub.Cur.Span, $"unexpected '{sub.Cur.Text}' in an interpolation");
            parts.Add(expr);
            interpolated = true;
            k = close;
        }
        Flush();
        if (!interpolated) return new StrLit(parts.Count == 0 ? "" : ((StrLit)parts[0]).Value);
        return new Interp(parts);
    }

    /// <summary>At an argument: is this 'x => ...' or '(a, b) => ...'?</summary>
    private bool AtLambda()
    {
        if (Cur.Kind == Tok.Ident) return Peek().Kind == Tok.Sym && Peek().Text == "=>";
        if (!IsSym("(")) return false;
        var k = 1;
        while (Peek(k).Kind == Tok.Ident)
        {
            var next = Peek(k + 1);
            if (next.Kind != Tok.Sym) return false;
            if (next.Text == ")") return Peek(k + 2).Kind == Tok.Sym && Peek(k + 2).Text == "=>";
            if (next.Text != ",") return false;
            k += 2;
        }
        return false;
    }

    private Lambda ParseLambda()
    {
        var start = Cur;
        var ps = new List<string>();
        if (TrySym("("))
        {
            do ps.Add(Ident("a lambda parameter").Text); while (TrySym(","));
            Sym(")");
        }
        else ps.Add(Ident("a lambda parameter").Text);
        Sym("=>");
        return At(start, new Lambda(ps, ParseExpr()));
    }

    private Expr ParsePrimary()
    {
        var start = Cur;
        if (Cur.Kind == Tok.Ident && Cur.Text == "await" && Peek().Kind == Tok.Ident)
            throw new CompileError("TN2029", start.Span, "'await' must be the whole value of a let, var, set, return or do statement",
                "Await into a local first: let x = await f(...)");
        if (Cur.Kind == Tok.Int) return At(start, new IntLit(ParseLong(Next())));
        if (Cur.Kind == Tok.Float)
        {
            var t = Next();
            return At(start, new FloatLit(double.Parse(t.Text, CultureInfo.InvariantCulture), t.Text));
        }
        if (Cur.Kind == Tok.Dec)
        {
            var t = Next();
            if (!decimal.TryParse(t.Text, NumberStyles.AllowDecimalPoint, CultureInfo.InvariantCulture, out var d))
                throw new CompileError("TN1001", t.Span, $"decimal literal '{t.Text}m' is out of range");
            return At(start, new DecLit(d, t.Text));
        }
        if (Cur.Kind == Tok.Str) return At(start, ParseString(Next()));
        if (TryKw("true")) return At(start, new BoolLit(true));
        if (TryKw("false")) return At(start, new BoolLit(false));
        if (TryKw("result")) return At(start, new Var("result"));
        if (TryKw("self")) return At(start, new Var("self"));
        if (TrySym("?")) return At(start, new Hole(Ident("a hole name").Text));
        if (TrySym("("))
        {
            if (TrySym(")")) return At(start, new UnitLit());
            var inner = ParseExpr();
            Sym(")");
            return inner;
        }
        if (TrySym("["))
        {
            var elems = new List<Expr>();
            if (!IsSym("]")) do elems.Add(ParseExpr()); while (TrySym(","));
            Sym("]");
            return At(start, new ArrayLit(elems));
        }
        if (TryKw("if"))
        {
            var c = ParseExpr();
            Kw("then");
            var t = ParseExpr();
            Kw("else");
            return At(start, new IfExpr(c, t, ParseExpr()));
        }
        if (TryKw("match"))
        {
            var scrutinee = ParseExpr();
            Sym("{");
            var arms = new List<(Pattern, Expr)>();
            while (!IsSym("}"))
            {
                var p = ParsePattern();
                Sym("=>");
                arms.Add((p, ParseExpr()));
                if (!TrySym(",")) break;
            }
            Sym("}");
            return At(start, new MatchExpr(scrutinee, arms));
        }
        if (IsKw("forall") || IsKw("exists")) return At(start, ParseQuant());
        if (TryKw("tensor")) return At(start, ParseTensorLit());
        if (Cur.Kind == Tok.Ident)
        {
            var name = Next();
            TType? shape = null;
            if (IsSym("[") && BracketThenParen())
            {
                Sym("[");
                shape = ParseShape(name);
                Sym("]");
            }
            if (!IsSym("("))
            {
                if (shape != null) throw Fail("expected '(' after the shape");
                return At(start, new Var(name.Text));
            }
            var (args, names) = ParseArgs();
            return At(start, new Call(name.Text, args, names) { ShapeArg = shape });
        }
        throw Fail($"expected an expression but found '{Cur.Text}'");
    }

    /// <summary>At '[': is this 'name[...](' (an explicit shape) rather than indexing?</summary>
    private bool BracketThenParen()
    {
        var depth = 0;
        for (var k = _p; k < toks.Count; k++)
        {
            if (toks[k].Kind != Tok.Sym) continue;
            if (toks[k].Text == "[") depth++;
            else if (toks[k].Text == "]" && --depth == 0) return k + 1 < toks.Count && toks[k + 1].Kind == Tok.Sym && toks[k + 1].Text == "(";
        }
        return false;
    }

    private Quant ParseQuant()
    {
        var forAll = Next().Text == "forall";
        var first = Ident("a bound variable name").Text;
        if (TryKw("in"))
        {
            if (Cur.Kind == Tok.Ident && Cur.Text == "elems" && Peek().Text == "(")
            {
                Next();
                Sym("(");
                var src = ParseExpr();
                Sym(")");
                Sym(":");
                return new Quant { ForAll = forAll, Kind = QuantKind.Elems, Binders = [(first, TType.Float)], Source = src, Body = ParseExpr() };
            }
            var lo = ParseAdd();
            Sym("..");
            var hi = ParseAdd();
            Sym(":");
            return new Quant { ForAll = forAll, Kind = QuantKind.Range, Binders = [(first, TType.Int)], Lo = lo, Hi = hi, Body = ParseExpr() };
        }
        Sym(":");
        var binders = new List<(string, TType)> { (first, ParseTypeRef()) };
        while (TrySym(","))
        {
            var n = Ident("a bound variable name").Text;
            Sym(":");
            binders.Add((n, ParseTypeRef()));
        }
        var triggers = new List<List<Expr>>();
        while (TryWord("trigger"))
        {
            var terms = new List<Expr>();
            do terms.Add(ParseUnary()); while (TrySym(","));
            triggers.Add(terms);
        }
        Sym(":");
        return new Quant { ForAll = forAll, Kind = QuantKind.Typed, Binders = binders, Triggers = triggers, Body = ParseExpr() };
    }

    private TensorLit ParseTensorLit()
    {
        Sym("[");
        var elem = ElemType.Float32;
        if (Cur.Kind == Tok.Ident && Cur.Text is "Float32" or "Float64" && Peek().Text == ";")
        {
            elem = Next().Text == "Float64" ? ElemType.Float64 : ElemType.Float32;
            Sym(";");
        }
        var shape = new List<long>();
        if (!IsSym("]"))
        {
            do
            {
                if (Cur.Kind != Tok.Int) throw Fail("a tensor literal's shape must be integer literals");
                shape.Add(ParseLong(Next()));
            } while (TrySym(","));
        }
        Sym("]");
        Sym("(");
        var values = new List<double>();
        var texts = new List<string>();
        do
        {
            var neg = TrySym("-");
            if (Cur.Kind is not (Tok.Int or Tok.Float)) throw Fail($"expected a number but found '{Cur.Text}'");
            var text = Next().Text;
            var v = double.Parse(text, CultureInfo.InvariantCulture);
            values.Add(neg ? -v : v);
            texts.Add(neg ? "-" + text : text);
        } while (TrySym(","));
        Sym(")");
        return new TensorLit(elem, shape, values, texts);
    }
}
