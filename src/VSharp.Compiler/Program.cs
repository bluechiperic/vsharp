using System.Diagnostics;
using System.Text.Json;

namespace VSharp.Compiler;

public sealed record CompileOptions(bool Verify = true, int TimeoutMs = 5000, string? SmtDir = null, bool Total = false, bool EntryChecks = true)
{
    /// <summary>Assemblies to search for attribute types, besides the .NET runtime.</summary>
    public IReadOnlyList<string> References { get; init; } = [];
}

public sealed record CompileResult(ModuleDecl? Module, List<Diagnostic> Diagnostics, bool Verified, int Queries)
{
    public bool Ok => Diagnostics.All(d => d.Severity != "error");
    /// <summary>The module's source texts, indexed like <see cref="Span.File"/> (the prelude comes last).</summary>
    public IReadOnlyList<string> Sources { get; init; } = [];
}

public static class Compilation
{
    /// <summary>Declarations every module can use without declaring them.</summary>
    public const string PreludeSource = """
        type Option[T] = | None | Some(value: T)
        type Result[T, E] = | Ok(value: T) | Err(error: E)
        """;

    /// <summary>Parses, checks and (unless disabled) verifies one source file.</summary>
    public static CompileResult Check(string source, string file, CompileOptions? options = null) => Check([(file, source)], options);

    /// <summary>
    /// Parses, checks and verifies a module split across several files. Every file starts with the same 'module' header;
    /// declarations from all files share one namespace, in file order. 'total' in a header applies to that file only.
    /// </summary>
    public static CompileResult Check(IReadOnlyList<(string Path, string Source)> files, CompileOptions? options = null)
    {
        options ??= new CompileOptions();
        var diags = new DiagnosticBag();
        ModuleDecl? module = null;
        var verified = false;
        var queries = 0;
        var sources = files.Select(f => f.Source).Append(PreludeSource).ToList();
        try
        {
            for (var k = 0; k < files.Count; k++)
            {
                ModuleDecl part;
                try
                {
                    part = new Parser(Lexer.Lex(files[k].Source, k)).ParseModule();
                }
                catch (CompileError e)
                {
                    diags.Error(e.Code, e.Span, e.Message, e.Hint);
                    continue;
                }
                module ??= new ModuleDecl { Name = part.Name, NameSpan = part.NameSpan };
                if (part.Name != module.Name)
                    diags.Error("TN2022", part.NameSpan, $"this file declares module '{part.Name}' but the module being compiled is '{module.Name}'",
                        $"Every file of a module starts with 'module {module.Name}'.");
                if (options.Total || part.TotalByDefault)
                    foreach (var f in part.Fns) f.Total = true;
                module.Types.AddRange(part.Types);
                module.Fns.AddRange(part.Fns);
                module.Consts.AddRange(part.Consts);
                module.Exceptions.AddRange(part.Exceptions);
                module.Holes.AddRange(part.Holes);
                module.Uses.AddRange(part.Uses);
            }
            if (module == null || diags.HasErrors) return Finish();

            var prelude = new ModuleDecl { Name = "Prelude" };
            new Parser(Lexer.Lex(PreludeSource, files.Count)).ParseDecls(prelude);
            foreach (var t in prelude.Types) t.Prelude = true;
            foreach (var f in prelude.Fns) f.Prelude = true;
            module.Types.InsertRange(0, prelude.Types);
            module.Fns.InsertRange(0, prelude.Fns);

            new Checker(module, diags, options.References).Check();
            if (!diags.HasErrors && options.Verify)
            {
                Action<string, string>? sink = null;
                if (options.SmtDir != null)
                {
                    Directory.CreateDirectory(options.SmtDir);
                    sink = (name, text) => File.WriteAllText(Path.Combine(options.SmtDir, name + ".smt2"), text);
                }
                var verifier = new Verifier(module, diags, sources, options.TimeoutMs, sink);
                verifier.Verify();
                queries = verifier.Queries;
                verified = !diags.HasErrors;
            }
            foreach (var h in module.Holes.Where(h => !diags.Items.Any(d => d.Code == "TN4001" && d.FileIndex == h.Span.File && d.Line == h.Span.Line && d.Col == h.Span.Col)))
                diags.Error("TN4001", h.Span, h.Type.IsError ? $"hole ?{h.Name} has a type that cannot be inferred here" : $"hole ?{h.Name} has type {h.Type}",
                    "Replace the hole with an expression of this type. Facts and obligations are listed once the rest of the module type-checks and verifies.");
        }
        catch (CompileError e)
        {
            diags.Error(e.Code, e.Span, e.Message, e.Hint);
        }
        return Finish();

        CompileResult Finish()
        {
            foreach (var d in diags.Items) d.File = d.FileIndex < files.Count ? files[d.FileIndex].Path : "<prelude>";
            return new CompileResult(module, diags.Items, verified, queries) { Sources = sources };
        }
    }

    /// <summary>Emits IL for a module that checked without errors. Returns the path of the assembly.</summary>
    public static string Emit(CompileResult result, string source, string outDir, bool entryChecks = true) =>
        new Emitter(result.Module!, result.Sources.Count > 0 ? result.Sources : [source], entryChecks).Emit(outDir, result.Verified);

    public static string Emit(CompileResult result, string outDir, bool entryChecks = true) =>
        new Emitter(result.Module!, result.Sources, entryChecks).Emit(outDir, result.Verified);
}

public static class Program
{
    private const string Usage = """
        vsharpc - the V# compiler

        usage:
          vsharpc check <files> [options]
          vsharpc build <files> [-o <dir>] [options]
          vsharpc run   <files> [-o <dir>] [options]
          vsharpc fmt   <files> [--write | --check]
          vsharpc sig   <files> [--json]
          vsharpc explain [<code>] [--json]

        <files> is one or more .vs files or directories (every .vs file in them); together they form one module.

        check     parse, type-check and verify; exit code 1 if anything fails
        build     check, then write <Module>.dll (IL) to the output directory (default: ./out)
        run       build, then execute the module's 'main' function
        fmt       print the canonical layout; --write rewrites the file, --check exits 1 if it is not canonical
        sig       print the module's types, signatures and contracts without bodies
        explain   describe a diagnostic code, or list them all

        options:
          --json               machine-readable output
          --timeout <ms>       solver time limit per proof obligation (default 5000)
          --emit-smt <dir>     write every SMT-LIB query to <dir>
          --no-verify          skip verification (the assembly is marked unverified)
          --total              prove every Int operation free of overflow, as if the module were declared 'total'
          --no-entry-checks    do not check preconditions and class invariants at public entry points
          --reference <dll>    (or -r) an assembly defining attribute types used with '@'; repeatable, copied to the output
        """;

    private static readonly JsonSerializerOptions Json = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
        // Keep quotes and comparison operators readable; the output is consumed by tools and models, not embedded in HTML.
        Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    public static int Main(string[] args)
    {
        if (args.Length >= 1 && args[0] == "explain") return ExplainCommand(args.Skip(1).ToArray());
        if (args.Length < 2 || args[0] is not ("check" or "build" or "run" or "fmt" or "sig"))
        {
            Console.Error.WriteLine(Usage);
            return 2;
        }
        var command = args[0];
        var inputs = args.Skip(1).TakeWhile(a => !a.StartsWith('-')).ToList();
        var json = false;
        var verify = true;
        var total = false;
        var entryChecks = true;
        var (write, checkOnly) = (false, false);
        var timeout = 5000;
        string? smtDir = null;
        var outDir = "out";
        var references = new List<string>();
        for (var i = 1 + inputs.Count; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--json": json = true; break;
                case "--no-verify": verify = false; break;
                case "--total": total = true; break;
                case "--no-entry-checks": entryChecks = false; break;
                case "--write" when command == "fmt": write = true; break;
                case "--check" when command == "fmt": checkOnly = true; break;
                case "--timeout" when i + 1 < args.Length && int.TryParse(args[i + 1], out var t): timeout = t; i++; break;
                case "--emit-smt" when i + 1 < args.Length: smtDir = args[++i]; break;
                case "-o" when i + 1 < args.Length: outDir = args[++i]; break;
                case "-r" or "--reference" when i + 1 < args.Length:
                    if (!File.Exists(args[i + 1]))
                    {
                        Console.Error.WriteLine($"reference not found: {args[i + 1]}");
                        return 2;
                    }
                    references.Add(Path.GetFullPath(args[++i]));
                    break;
                default:
                    Console.Error.WriteLine($"unknown or incomplete option '{args[i]}'\n\n{Usage}");
                    return 2;
            }
        }
        var paths = new List<string>();
        foreach (var input in inputs)
        {
            if (Directory.Exists(input)) paths.AddRange(Directory.GetFiles(input, "*.vs").Order(StringComparer.Ordinal));
            else if (File.Exists(input)) paths.Add(input);
            else
            {
                Console.Error.WriteLine($"file not found: {input}");
                return 2;
            }
        }
        if (paths.Count == 0)
        {
            Console.Error.WriteLine("no .vs files given");
            return 2;
        }
        var files = paths.Select(p => (Path: p, Source: File.ReadAllText(p))).ToList();

        if (command is "fmt" or "sig")
        {
            var status = 0;
            foreach (var (path, source) in files) status = Math.Max(status, Layout(command, path, source, write, checkOnly, json));
            return status;
        }

        var result = Compilation.Check(files, new CompileOptions(verify, timeout, smtDir, total, entryChecks) { References = references });
        string? dll = null;
        if (result.Ok && command != "check")
        {
            dll = Compilation.Emit(result, outDir, entryChecks);
            foreach (var r in references) File.Copy(r, Path.Combine(outDir, Path.GetFileName(r)), overwrite: true);
        }
        Report(result, json, dll);
        if (!result.Ok) return 1;
        if (command != "run") return 0;

        if (result.Module!.Fns.All(f => f.Name != "main"))
        {
            Console.Error.WriteLine("nothing to run: the module has no 'main' function");
            return 2;
        }
        using var process = Process.Start(new ProcessStartInfo("dotnet", [dll!]) { UseShellExecute = false })!;
        process.WaitForExit();
        return process.ExitCode;
    }

    private static int Layout(string command, string file, string source, bool write, bool checkOnly, bool json)
    {
        string text;
        try
        {
            text = command == "fmt" ? Formatter.Format(source) : Formatter.Signatures(source);
        }
        catch (CompileError e)
        {
            Console.Error.WriteLine($"{file}({e.Span.Line},{e.Span.Col}): error {e.Code}: {e.Message}");
            return 1;
        }
        if (command == "sig")
        {
            if (json) Console.WriteLine(JsonSerializer.Serialize(new { file, signatures = text }, Json));
            else Console.Write(text);
            return 0;
        }
        var canonical = source.Replace("\r\n", "\n") == text;
        if (checkOnly)
        {
            if (!canonical) Console.Error.WriteLine($"{file}: not in canonical form (run 'vsharpc fmt {file} --write')");
            return canonical ? 0 : 1;
        }
        if (write)
        {
            if (!canonical) File.WriteAllText(file, text);
            return 0;
        }
        Console.Write(text);
        return 0;
    }

    private static int ExplainCommand(string[] args)
    {
        var json = args.Contains("--json");
        var code = args.FirstOrDefault(a => !a.StartsWith("--", StringComparison.Ordinal));
        var entries = code == null ? Explain.All : Explain.Find(code) is { } e ? [e] : [];
        if (entries.Count == 0)
        {
            Console.Error.WriteLine($"unknown diagnostic code '{code}'. Run 'vsharpc explain' to list them.");
            return 2;
        }
        if (json)
        {
            Console.WriteLine(JsonSerializer.Serialize(entries, Json));
            return 0;
        }
        if (code == null)
        {
            foreach (var x in entries) Console.WriteLine($"{x.Code}  {x.Title}");
            return 0;
        }
        var entry = entries[0];
        Console.WriteLine($"{entry.Code}: {entry.Title}\n\n{entry.Text}");
        if (entry.Example != null) Console.WriteLine($"\nexample:\n  {entry.Example.Replace("\n", "\n  ")}");
        return 0;
    }

    private static void Report(CompileResult result, bool json, string? dll)
    {
        if (json)
        {
            Console.WriteLine(JsonSerializer.Serialize(
                new { ok = result.Ok, verified = result.Verified, queries = result.Queries, output = dll, diagnostics = result.Diagnostics }, Json));
            return;
        }
        foreach (var d in result.Diagnostics)
        {
            Console.Error.WriteLine($"{d.File}({d.Line},{d.Col}): {d.Severity} {d.Code}: {d.Message}");
            if (d.Counterexample != null)
                Console.Error.WriteLine("  counterexample: " + string.Join(", ", d.Counterexample.Select(kv => $"{kv.Key} = {kv.Value}")));
            if (d.InScope is { Count: > 0 })
                Console.Error.WriteLine("  in scope: " + string.Join(", ", d.InScope.Select(kv => $"{kv.Key}: {kv.Value}")));
            if (d.Facts is { Count: > 0 })
                foreach (var f in d.Facts) Console.Error.WriteLine("  known: " + f);
            if (d.Obligations is { Count: > 0 })
                foreach (var o in d.Obligations) Console.Error.WriteLine("  must satisfy: " + o);
            if (d.Hint != null) Console.Error.WriteLine("  hint: " + d.Hint);
        }
        if (!result.Ok) return;
        var proof = result.Verified ? $"verified ({result.Queries} proof obligations discharged)" : "NOT verified (--no-verify)";
        Console.Error.WriteLine(dll == null ? $"ok: {proof}" : $"ok: {proof} -> {dll}");
    }
}
