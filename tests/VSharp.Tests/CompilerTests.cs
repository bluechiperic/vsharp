using System.Diagnostics;
using System.Reflection;
using System.Text.RegularExpressions;
using VSharp.Compiler;
using VSharp.Runtime;
using Check = Xunit.Assert;

namespace VSharp.Tests;

public class CompilerTests
{
    private static readonly string Root = FindRoot();

    private static string FindRoot()
    {
        var dir = new DirectoryInfo(AppContext.BaseDirectory);
        while (dir != null && !File.Exists(Path.Combine(dir.FullName, "VSharp.sln"))) dir = dir.Parent;
        return dir?.FullName ?? throw new InvalidOperationException("VSharp.sln not found above the test directory");
    }

    private static (CompileResult Result, string Source) Compile(string relativePath)
    {
        var path = Path.Combine(Root, relativePath);
        var source = File.ReadAllText(path);
        return (Compilation.Check(source, path), source);
    }

    // Each sample is built once: a loaded assembly locks its file, so rebuilding to the same path would fail.
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<string, Lazy<string>> Built = new();

    private static string Build(string sample) => Built.GetOrAdd(sample, s => new Lazy<string>(() => BuildOnce(s))).Value;

    private static string BuildOnce(string sample)
    {
        var (result, source) = Compile(Path.Combine("samples", sample));
        Check.True(result.Ok, string.Join("\n", result.Diagnostics.Select(d => $"{d.Code} {d.Line}:{d.Col} {d.Message}")));
        Check.True(result.Verified);
        return Compilation.Emit(result, source, TempDir());
    }

    private static string TempDir() => Path.Combine(Path.GetTempPath(), "vsharp-tests", Guid.NewGuid().ToString("N"));

    private static Type BuildSource(string source, string module)
    {
        var result = Compilation.Check(source, module + ".vs");
        Check.True(result.Ok, string.Join("\n", result.Diagnostics.Select(d => $"{d.Code} {d.Line}:{d.Col} {d.Message}")));
        return Assembly.LoadFile(Compilation.Emit(result, source, TempDir())).GetType(module)!;
    }

    // ---------- samples ----------

    [Theory]
    [InlineData("verified_math.vs", "42\n100\n12586269025\n21\n")]
    [InlineData("search.vs", "[0, 1, 4, 9, 16, 25, 36, 49]\n5\n-1\n1\n")]
    [InlineData("mlp.vs", "[[2.5, 3.05], [1.3, 2.3]]\n[[1, -1], [2, 0.5], [3, 2]]\n")]
    [InlineData("types.vs", "48\n60\n0\n7\nOk(value: 3)\nErr(error: 7)\nSome(value: 10)\n-1\nPair(first: true, second: 1)\n[5, 4, 3, 2, 1]\n")]
    [InlineData("proofs.vs", "5050\n5050\n1\ntrue\ntrue\n9\n6\n")]
    [InlineData("total.vs", "6\n1006\n")]
    [InlineData("floats.vs", "1\n0\n5\n2.5\n25\n")]
    [InlineData("shapes.vs", "Rect(width: 2, height: 3)\n6\n4\n10\n40\nTriangle(base: 4, height: 5)\n3\ntrue\n")]
    [InlineData("async.vs", "Missing\nValue(n: 7)\n15\n3\n5\ndone\n")]
    [InlineData("exceptions.vs", "70\nErr(error: \"cannot withdraw 500 from 100\")\nErr(error: \"account is frozen\")\n" +
        "Ok(value: Account(owner: \"alice\", balance: 60, frozen: false))\ntransfer refused: 200 > 100\n2\n12.50\n0\n20\n0\nbob is frozen\n")]
    [InlineData("business.vs", """
        Ann on 2024-02-29: 75 min
        2024-03-04
        2024-02-29
        19.50
        [Visit(patient: "Ann", day: 2024-02-29, minutes: 75, fee: 12.50)]
        1
        2
        0
        Some(value: Visit(patient: "Ann", day: 2024-02-29, minutes: 75, fee: 12.50))
        None
        5
        1
        {"a": 2, "b": 1}
        Visit(patient: "Cy", day: 2024-03-01, minutes: 30, fee: 7)
        2.35
        -2.35
        true
        [Visit(patient: "Ann", day: 2024-02-29, minutes: 75, fee: 12.50), Visit(patient: "Bob", day: 2024-03-01, minutes: 30, fee: 7)]
        [75, 30]
        {true: [Visit(patient: "Ann", day: 2024-02-29, minutes: 75, fee: 12.50)], false: [Visit(patient: "Bob", day: 2024-03-01, minutes: 30, fee: 7)]}
        Some(value: Visit(patient: "Ann", day: 2024-02-29, minutes: 75, fee: 12.50))
        105
        Some(value: 2024-12-01)
        None
        42
        true
        2
        ["a", "b", "", "c"]
        4

        """)]
    public void Sample_verifies_compiles_to_il_and_runs(string sample, string expectedOutput)
    {
        Check.Equal(expectedOutput.Replace("\r\n", "\n").Replace("\r", "\n"), Run(Build(sample)));
    }

    [Fact]
    public void Training_sample_learns_xor()
    {
        var lines = Run(Build("train.vs")).Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var losses = lines.Take(4).Select(l => double.Parse(l, System.Globalization.CultureInfo.InvariantCulture)).ToList();
        Check.True(losses[0] > 0.5 && losses[^1] < 0.01, $"loss should fall from ~1 to near 0: {string.Join(", ", losses)}");
        var predictions = Regex.Matches(lines[4], @"[\d.]+").Select(m => double.Parse(m.Value, System.Globalization.CultureInfo.InvariantCulture)).ToList();
        Check.Equal([false, true, true, false], predictions.Select(p => p > 0.5));
    }

    private static string Run(string dll)
    {
        using var process = Process.Start(new ProcessStartInfo("dotnet", [dll]) { RedirectStandardOutput = true, RedirectStandardError = true })!;
        var stdout = process.StandardOutput.ReadToEnd();
        var stderr = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Check.True(process.ExitCode == 0, stderr);
        return stdout.Replace("\r\n", "\n");
    }

    // ---------- rejected programs ----------

    public static IEnumerable<object[]> FailCases() =>
        Directory.GetFiles(Path.Combine(Root, "tests", "cases", "fail"), "*.vs").Select(f => new object[] { Path.GetFileName(f) });

    [Theory]
    [MemberData(nameof(FailCases))]
    public void Incorrect_program_is_rejected_with_the_expected_codes(string file)
    {
        var (result, source) = Compile(Path.Combine("tests", "cases", "fail", file));
        var expected = Regex.Match(source, @"// expect: ([^\r\n]*)").Groups[1].Value.Split(' ', StringSplitOptions.RemoveEmptyEntries).Order();
        Check.Equal(expected, result.Diagnostics.Select(d => d.Code).Distinct().Order());
    }

    [Fact]
    public void Refuted_obligation_reports_a_counterexample_that_really_violates_the_contract()
    {
        var (result, _) = Compile(Path.Combine("tests", "cases", "fail", "postcondition.vs"));
        var d = Check.Single(result.Diagnostics);
        Check.Equal("refuted", d.Status);
        Check.True(long.Parse(d.Counterexample!["x"]) < 0, "abs returns x unchanged, so only a negative x breaks 'result >= 0'");
        Check.Equal(d.Counterexample["x"], d.Counterexample["result"]);
    }

    [Fact]
    public void Floating_point_counterexample_can_be_nan()
    {
        var (result, _) = Compile(Path.Combine("tests", "cases", "fail", "nan.vs"));
        var d = Check.Single(result.Diagnostics);
        Check.Equal("NaN", d.Counterexample!["x"]);
    }

    [Fact]
    public void Typed_hole_reports_its_type_scope_facts_and_obligations()
    {
        var (result, _) = Compile(Path.Combine("tests", "cases", "fail", "hole.vs"));
        var d = Check.Single(result.Diagnostics);
        Check.Equal("TN4001", d.Code);
        Check.Contains("Int", d.Message);
        Check.Equal(new Dictionary<string, string> { ["a"] = "Int", ["b"] = "Int" }, d.InScope);
        Check.Contains("!(a > b)", d.Facts!);
        Check.Contains(d.Obligations!, o => o.Contains("result >= a && result >= b"));
    }

    [Fact]
    public void Every_diagnostic_code_has_an_explanation()
    {
        var codes = Directory.GetFiles(Path.Combine(Root, "src", "VSharp.Compiler"), "*.cs")
            .Where(f => !f.EndsWith("Explain.cs"))
            .SelectMany(f => Regex.Matches(File.ReadAllText(f), "\"(TN\\d{4})\"").Select(m => m.Groups[1].Value))
            .Distinct().Order().ToList();
        Check.NotEmpty(codes);
        Check.All(codes, c => Check.NotNull(Explain.Find(c)));
    }

    // ---------- emitted IL ----------

    [Fact]
    public void Emitted_assembly_is_callable_from_dotnet_and_carries_its_contracts()
    {
        var type = Assembly.LoadFile(Build("verified_math.vs")).GetType("VerifiedMath")!;
        Check.NotNull(type.GetCustomAttribute<VerifiedAttribute>());

        var fib = type.GetMethod("fib_fast")!;
        Check.Equal(typeof(long), fib.ReturnType);
        Check.Equal(55L, fib.Invoke(null, [10L]));
        Check.Equal(
            [("requires", "n >= 0"), ("ensures", "result == fib(n)")],
            fib.GetCustomAttributes<ContractAttribute>().Select(c => (c.Kind, c.Text)));
    }

    [Fact]
    public void Integer_overflow_traps_instead_of_wrapping()
    {
        // fib(100) does not fit in 64 bits. The proof is about unbounded integers, so the IL must not silently wrap.
        var fib = Assembly.LoadFile(Build("verified_math.vs")).GetType("VerifiedMath")!.GetMethod("fib_fast")!;
        var error = Check.Throws<TargetInvocationException>(() => fib.Invoke(null, [100L]));
        Check.IsType<OverflowException>(error.InnerException);
    }

    [Fact]
    public void Public_entry_points_check_preconditions_and_refinements_for_unverified_callers()
    {
        var math = Assembly.LoadFile(Build("verified_math.vs")).GetType("VerifiedMath")!;
        var clamp = math.GetMethod("clamp")!;
        Check.Equal(5L, clamp.Invoke(null, [9L, 0L, 5L]));
        var e = Check.Throws<TargetInvocationException>(() => clamp.Invoke(null, [9L, 5L, 0L]));
        var violation = Check.IsType<ContractViolationException>(e.InnerException);
        Check.Contains("lo <= hi", violation.Message);

        var types = Assembly.LoadFile(Build("types.vs")).GetType("Types")!;
        var countdown = types.GetMethod("countdown")!;
        Check.Equal(new long[] { 2, 1 }, countdown.Invoke(null, [2L]));
        e = Check.Throws<TargetInvocationException>(() => countdown.Invoke(null, [-1L]));
        Check.Contains("Nat", Check.IsType<ContractViolationException>(e.InnerException).Message);
    }

    [Fact]
    public void Unions_and_generics_are_ordinary_clr_types()
    {
        var asm = Assembly.LoadFile(Build("types.vs"));
        var option = asm.GetType("Option`1")!;
        var some = asm.GetType("Some`1")!;
        Check.True(option.IsAbstract && option.IsGenericTypeDefinition);
        Check.Equal(option, some.BaseType!.GetGenericTypeDefinition());

        var first = asm.GetType("Types")!.GetMethod("first")!.MakeGenericMethod(typeof(string));
        var r = first.Invoke(null, [new[] { "a", "b" }])!;
        Check.Equal(some.MakeGenericType(typeof(string)), r.GetType());
        Check.Equal("a", r.GetType().GetProperty("value")!.GetValue(r));
    }

    [Fact]
    public void Records_are_dotnet_friendly_dtos_with_structural_equality()
    {
        var asm = Assembly.LoadFile(Build("business.vs"));
        var visit = asm.GetType("Visit")!;
        Check.Equal(["patient", "day", "minutes", "fee"], visit.GetProperties().Select(p => p.Name));
        Check.Equal([typeof(string), typeof(DateOnly), typeof(int), typeof(decimal)], visit.GetProperties().Select(p => p.PropertyType));
        Check.Empty(visit.GetFields());

        object Make(string who, decimal fee) => Activator.CreateInstance(visit, who, new DateOnly(2024, 2, 29), 75, fee)!;
        var (a, b) = (Make("Ann", 12.50m), Make("Ann", 12.5m));
        Check.Equal(a, b);
        Check.Equal(a.GetHashCode(), b.GetHashCode());
        Check.NotEqual(a, Make("Bob", 12.5m));
        Check.Equal("""{"patient":"Ann","day":"2024-02-29","minutes":75,"fee":12.50}""", System.Text.Json.JsonSerializer.Serialize(a, visit));

        var business = asm.GetType("Business")!;
        Check.Equal("Ann on 2024-02-29: 75 min", business.GetMethod("label")!.Invoke(null, [a]));
        var tally = business.GetMethod("tally")!.Invoke(null, [new[] { "x", "y", "x" }]);
        var counts = Check.IsAssignableFrom<IReadOnlyDictionary<string, long>>(tally);
        Check.Equal(2L, counts["x"]);
        Check.Equal(["x", "y"], counts.Keys);
    }

    /// <summary>A .NET implementation of a V# interface, as a mocking library would generate.</summary>
    public class FixedShape : DispatchProxy
    {
        protected override object? Invoke(MethodInfo? method, object?[]? args) => method!.Name == "area" ? 5m : 4L;
    }

    [Fact]
    public void Classes_and_interfaces_are_clr_types_that_dotnet_code_can_implement_and_mock()
    {
        var asm = Assembly.LoadFile(Build("shapes.vs"));
        var shape = asm.GetType("Shape")!;
        var rect = asm.GetType("Rect")!;
        Check.True(shape.IsInterface);
        Check.True(rect.IsSealed && shape.IsAssignableFrom(rect));
        Check.Equal(typeof(decimal), shape.GetMethod("area")!.ReturnType);

        var r = Activator.CreateInstance(rect, 2m, 3m)!;
        Check.Equal(6m, shape.GetMethod("area")!.Invoke(r, []));
        Check.Equal(24m, rect.GetMethod("area")!.Invoke(rect.GetMethod("scaled")!.Invoke(r, [2m]), []));
        Check.Contains(("ensures", "result > 0m"), rect.GetMethod("area")!.GetCustomAttributes<ContractAttribute>().Select(c => (c.Kind, c.Text)));

        var e = Check.Throws<TargetInvocationException>(() => rect.GetMethod("scaled")!.Invoke(r, [0m]));
        Check.Contains("k > 0m", Check.IsType<ContractViolationException>(e.InnerException).Message);
        e = Check.Throws<TargetInvocationException>(() => Activator.CreateInstance(rect, -1m, 3m));
        Check.Contains("self.width > 0m", Check.IsType<ContractViolationException>(e.InnerException).Message);

        var mock = DispatchProxy.Create(shape, typeof(FixedShape));
        var shapes = Array.CreateInstance(shape, 2);
        shapes.SetValue(mock, 0);
        shapes.SetValue(r, 1);
        Check.Equal(11m, asm.GetType("Shapes")!.GetMethod("total_area")!.Invoke(null, [shapes]));
    }

    /// <summary>A .NET implementation of an async V# interface: odd keys finish at once, even keys later, 99 fails.</summary>
    public class SlowSource : DispatchProxy
    {
        protected override object? Invoke(MethodInfo? method, object?[]? args)
        {
            var key = (long)args![0]!;
            if (key == 99) return Task.FromException<long>(new InvalidOperationException("offline"));
            if (key % 2 == 1) return Task.FromResult(key * 10);
            return Task.Run(async () => { await Task.Delay(5); return key * 10; });
        }
    }

    [Fact]
    public async Task Async_functions_return_tasks_that_dotnet_code_can_await()
    {
        var asm = Assembly.LoadFile(Build("async.vs"));
        var tasks = asm.GetType("Tasks")!;
        var source = asm.GetType("Source")!;
        Check.Equal(typeof(Task<long>), source.GetMethod("fetch")!.ReturnType);
        Check.Equal(typeof(Task<long>), tasks.GetMethod("twice")!.ReturnType);

        var doubler = Activator.CreateInstance(asm.GetType("Doubler")!, 1L)!;
        Check.Equal(5L, await (Task<long>)source.GetMethod("fetch")!.Invoke(doubler, [2L])!);

        var mock = DispatchProxy.Create(source, typeof(SlowSource));
        Check.Equal(30L, await (Task<long>)tasks.GetMethod("twice")!.Invoke(null, [mock, 3L])!);
        Check.Equal(60L, await (Task<long>)tasks.GetMethod("sum_all")!.Invoke(null, [mock, 4L])!);

        var failed = (Task<long>)tasks.GetMethod("twice")!.Invoke(null, [mock, 99L])!;
        Check.Equal("offline", (await Check.ThrowsAsync<InvalidOperationException>(() => failed)).Message);

        var e = Check.Throws<TargetInvocationException>(() => tasks.GetMethod("twice")!.Invoke(null, [mock, -1L]));
        Check.Contains("key >= 0", Check.IsType<ContractViolationException>(e.InnerException).Message);
    }

    [Fact]
    public async Task Exceptions_are_clr_exception_classes_that_dotnet_code_can_catch()
    {
        var asm = Assembly.LoadFile(Build("exceptions.vs"));
        var ledger = asm.GetType("Ledger")!;
        var overdrawn = asm.GetType("Overdrawn")!;
        var frozen = asm.GetType("Frozen")!;
        Check.True(overdrawn.IsSealed && overdrawn.BaseType == typeof(Exception));

        var account = asm.GetType("Account")!;
        var alice = Activator.CreateInstance(account, "alice", 100m, false)!;
        var bob = Activator.CreateInstance(account, "bob", 5m, true)!;
        var withdraw = ledger.GetMethod("withdraw")!;
        Check.Contains(("throws", "Overdrawn when !a.frozen && amount > a.balance"),
            withdraw.GetCustomAttributes<ContractAttribute>().Select(c => (c.Kind, c.Text)));

        var e = Check.Throws<TargetInvocationException>(() => withdraw.Invoke(null, [alice, 500m]));
        Check.IsType(overdrawn, e.InnerException);
        Check.Equal(500m, overdrawn.GetProperty("amount")!.GetValue(e.InnerException));
        Check.Equal("Overdrawn(balance: 100, amount: 500)", e.InnerException!.Message);
        Check.NotNull(e.InnerException.StackTrace);
        Check.Equal(60m, account.GetProperty("balance")!.GetValue(withdraw.Invoke(null, [alice, 40m])));

        var later = (Task)ledger.GetMethod("withdraw_later")!.Invoke(null, [bob, 1m])!;
        var thrown = await Check.ThrowsAnyAsync<Exception>(() => later);
        Check.IsType(frozen, thrown);

        var rates = asm.GetType("Rates")!;
        var mock = DispatchProxy.Create(rates, typeof(EuroOnlyRates));
        ((EuroOnlyRates)mock).Unknown = asm.GetType("UnknownCurrency")!;
        var convert = ledger.GetMethod("convert")!;
        Check.Equal(30m, convert.Invoke(null, [mock, 10m, "EUR"]));
        Check.Equal(0m, convert.Invoke(null, [mock, 10m, "USD"]));
    }

    /// <summary>A .NET implementation of a V# interface that throws the exception the interface declares.</summary>
    public class EuroOnlyRates : DispatchProxy
    {
        public Type Unknown { get; set; } = null!;

        protected override object? Invoke(MethodInfo? method, object?[]? args) =>
            (string)args![0]! == "EUR" ? 3m : throw (Exception)Activator.CreateInstance(Unknown, args[0])!;
    }

    [Fact]
    public void Invariants_and_inherited_contracts_are_usable_in_proofs()
    {
        const string source = """
            module Accounts

            interface Account {
              fn withdraw(self, amount: Int) -> Int
                requires amount > 0
                ensures result >= 0

              fn balance(self) -> Int
                ensures result >= 0
            }

            spec fn positive(n: Int) -> Bool {
              n >= 0
            }

            class Wallet(cash: Int) implements Account {
              invariant positive(self.cash)

              fn withdraw(self, amount: Int) -> Int
                ensures result <= self.cash
              {
                if amount > self.cash { return 0 }
                return self.cash - amount
              }

              fn balance(self) -> Int {
                return self.cash
              }
            }

            class Vault(gold: Int) implements Account {
              invariant self.gold >= 100

              fn withdraw(self, amount: Int) -> Int {
                return self.gold
              }

              fn balance(self) -> Int {
                return self.gold
              }
            }

            fn pick(rich: Bool) -> Account {
              return if rich then Vault(gold: 500) else Wallet(cash: 5)
            }

            fn via(a: Account) -> Int
              ensures result >= 0
            {
              return a.withdraw(3) + a.balance()
            }
            """;
        var accounts = BuildSource(source, "Accounts");
        object? Via(bool rich) => accounts.GetMethod("via")!.Invoke(null, [accounts.GetMethod("pick")!.Invoke(null, [rich])]);
        Check.Equal(1000L, Via(true));
        Check.Equal(7L, Via(false));

        var direct = Compilation.Check(source + "\nfn direct(w: Wallet) -> Int {\n  return w.withdraw(0)\n}\n", "Accounts.vs");
        var d = Check.Single(direct.Diagnostics);
        Check.Equal("TN3002", d.Code);
        Check.Contains("amount > 0", d.Message);
    }

    [Fact]
    public void Attributes_are_emitted_on_the_dotnet_members()
    {
        var asm = Assembly.LoadFile(Build("shapes.vs"));
        var rect = asm.GetType("Rect")!;
        Check.Equal("An axis-aligned rectangle", rect.GetCustomAttribute<System.ComponentModel.DescriptionAttribute>()!.Description);
        Check.Equal("""{"w":2,"h":3}""", System.Text.Json.JsonSerializer.Serialize(Activator.CreateInstance(rect, 2m, 3m), rect));
        Check.Equal("Use total_area", asm.GetType("Shapes")!.GetMethod("area_of_two")!.GetCustomAttribute<ObsoleteAttribute>()!.Message);
    }

    [Fact]
    public void Attribute_types_can_come_from_a_referenced_assembly()
    {
        // An assembly that is neither loaded nor part of the .NET runtime, as a NuGet package's would be.
        var refDir = TempDir();
        Directory.CreateDirectory(refDir);
        var name = "Tags" + Guid.NewGuid().ToString("N");
        var ab = new System.Reflection.Emit.PersistedAssemblyBuilder(new AssemblyName(name), typeof(object).Assembly);
        var tb = ab.DefineDynamicModule(name).DefineType($"{name}.TagAttribute", TypeAttributes.Public | TypeAttributes.Sealed, typeof(Attribute));
        var ctor = tb.DefineConstructor(MethodAttributes.Public, CallingConventions.Standard, [typeof(string)]);
        var il = ctor.GetILGenerator();
        il.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
        il.Emit(System.Reflection.Emit.OpCodes.Call, typeof(Attribute).GetConstructor(BindingFlags.NonPublic | BindingFlags.Instance, Type.EmptyTypes)!);
        il.Emit(System.Reflection.Emit.OpCodes.Ret);
        tb.CreateType();
        var refPath = Path.Combine(refDir, name + ".dll");
        ab.Save(refPath);

        var source = $"module Tagged\n\nuse {name}\n\n@Tag(\"billing\")\nfn f(x: Int) -> Int {{\n  return x\n}}\n";
        var missing = Compilation.Check(source, "Tagged.vs");
        Check.Contains(missing.Diagnostics, d => d.Code == "TN2026" && d.Message.Contains("unknown attribute 'Tag'"));

        var result = Compilation.Check([("Tagged.vs", source)], new CompileOptions { References = [refPath] });
        Check.True(result.Ok, string.Join("\n", result.Diagnostics.Select(d => $"{d.Code} {d.Message}")));
        var data = Assembly.LoadFile(Compilation.Emit(result, TempDir())).GetType("Tagged")!.GetMethod("f")!.GetCustomAttributesData();
        var tag = Check.Single(data, a => a.AttributeType.Name == "TagAttribute");
        Check.Equal("billing", tag.ConstructorArguments[0].Value);
    }

    [Fact]
    public void Entry_checks_cover_dates_and_collection_preconditions()
    {
        var business = Assembly.LoadFile(Build("business.vs")).GetType("Business")!;
        var nextWeek = business.GetMethod("next_week")!;
        Check.Equal(new DateOnly(2024, 3, 7), nextWeek.Invoke(null, [new DateOnly(2024, 2, 29)]));
        var e = Check.Throws<TargetInvocationException>(() => nextWeek.Invoke(null, [new DateOnly(1999, 12, 31)]));
        Check.IsType<ContractViolationException>(e.InnerException);
    }

    [Fact]
    public void A_module_can_span_several_files()
    {
        var files = new List<(string, string)>
        {
            ("a.vs", "module Split\n\ntype Slot = { start: Int32, minutes: Int32 }\n\nconst DAY: Int = 1440\n"),
            ("b.vs", "module Split\n\nfn ends(s: Slot) -> Int\n  requires s.start >= 0 && s.minutes >= 0\n  ensures result >= 0\n{\n  return to_int(s.start) + to_int(s.minutes) % DAY\n}\n"),
        };
        var result = Compilation.Check(files);
        Check.True(result.Ok, string.Join("\n", result.Diagnostics.Select(d => $"{d.File} {d.Code} {d.Message}")));
        var type = Assembly.LoadFile(Compilation.Emit(result, TempDir())).GetType("Split")!;
        var slot = type.Assembly.GetType("Slot")!;
        Check.Equal(130L, type.GetMethod("ends")!.Invoke(null, [Activator.CreateInstance(slot, 70, 60)]));

        files.Add(("c.vs", "module Other\n\nfn broken() -> Int {\n  return str_len(1)\n}\n"));
        var bad = Compilation.Check(files);
        var mismatch = Check.Single(bad.Diagnostics, d => d.Code == "TN2022");
        Check.Equal("c.vs", mismatch.File);
        Check.Equal(1, mismatch.Line);
    }

    [Fact]
    public void The_scheduling_port_verifies_and_can_be_referenced_from_csharp()
    {
        var dir = Path.Combine(Root, "samples", "scheduling");
        var files = Directory.GetFiles(dir, "*.vs").Order().Select(f => (f, File.ReadAllText(f))).ToList();
        var result = Compilation.Check(files);
        Check.True(result.Ok, string.Join("\n", result.Diagnostics.Select(d => $"{d.File} {d.Code} {d.Line}:{d.Col} {d.Message}")));
        Check.True(result.Verified);
        var dll = Compilation.Emit(result, TempDir());

        // Compilers only see reference assemblies, so the module must name System.Runtime rather than CoreLib.
        using (var pe = new System.Reflection.PortableExecutable.PEReader(File.OpenRead(dll)))
        {
            var md = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
            var refs = md.AssemblyReferences.Select(h => md.GetString(md.GetAssemblyReference(h).Name)).ToList();
            Check.Contains("System.Runtime", refs);
            Check.DoesNotContain("System.Private.CoreLib", refs);
        }
        var type = Assembly.LoadFile(dll).GetType("Scheduling")!;
        Check.Equal("13", type.GetMethod("whole")!.Invoke(null, [12.5m]));
    }

    [Fact]
    public void Diagnostics_point_at_the_file_that_contains_the_error()
    {
        var result = Compilation.Check(
        [
            ("ok.vs", "module Two\n\nfn one() -> Int {\n  return 1\n}\n"),
            ("bad.vs", "module Two\n\nfn half(x: Int) -> Int {\n  return 10 / x\n}\n"),
        ]);
        var d = Check.Single(result.Diagnostics);
        Check.Equal(("TN3006", "bad.vs", 4), (d.Code, d.File, d.Line));
    }

    [Fact]
    public void Ghost_code_is_erased()
    {
        // index_of_max keeps a ghost step counter for its proof; only 'best' and 'i' exist at run time.
        var type = Assembly.LoadFile(Build("proofs.vs")).GetType("Proofs")!;
        var impl = type.GetMethod("index_of_max$impl", BindingFlags.NonPublic | BindingFlags.Static)!;
        Check.Equal(2, impl.GetMethodBody()!.LocalVariables.Count);
        Check.Null(type.GetMethod("sum_to", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static));
        Check.Null(type.GetMethod("sum_formula", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static));
    }

    [Fact]
    public void Extern_functions_call_dotnet_methods()
    {
        var floats = Assembly.LoadFile(Build("floats.vs")).GetType("Floats")!;
        Check.Equal(13.0, floats.GetMethod("distance")!.Invoke(null, [5.0, 12.0]));
    }

    // ---------- autodiff ----------

    private const string GradSource = """
        module GradCheck

        fn loss[B](x: Tensor[Float64; B, 3], w: Tensor[Float64; 3, 2], b: Tensor[Float64; 2]) -> Float {
          let h = add_bias(matmul(x, w), b)
          let s = softmax(tanh(h))
          let t = sub(s, scale(transpose(transpose(sigmoid(h))), 0.3))
          return sum(mul(t, s)) * 2.0 + sum(h) / 4.0
        }

        fn dx = grad loss wrt x
        fn dw = grad loss wrt w
        fn db = grad loss wrt b
        """;

    [Fact]
    public void Grad_matches_finite_differences()
    {
        var type = BuildSource(GradSource, "GradCheck");
        var rng = new Random(7);
        Tensor<double> Rand(params int[] shape) => new(Enumerable.Range(0, shape.Aggregate(1, (a, b) => a * b)).Select(_ => rng.NextDouble() * 2 - 1).ToArray(), shape);
        var args = new[] { Rand(4, 3), Rand(3, 2), Rand(2) };
        var loss = type.GetMethod("loss")!;
        double L(Tensor<double>[] a) => (double)loss.Invoke(null, a)!;

        foreach (var (name, k) in new[] { ("dx", 0), ("dw", 1), ("db", 2) })
        {
            var analytic = (Tensor<double>)type.GetMethod(name)!.Invoke(null, args)!;
            Check.Equal(args[k].Shape, analytic.Shape);
            for (var i = 0; i < args[k].Data.Length; i++)
            {
                const double h = 1e-6;
                var saved = args[k].Data[i];
                args[k].Data[i] = saved + h;
                var up = L(args);
                args[k].Data[i] = saved - h;
                var down = L(args);
                args[k].Data[i] = saved;
                var numeric = (up - down) / (2 * h);
                Check.True(Math.Abs(numeric - analytic.Data[i]) < 1e-6 * Math.Max(1, Math.Abs(numeric)),
                    $"{name}[{i}]: analytic {analytic.Data[i]}, numeric {numeric}");
            }
        }
    }

    // ---------- device ----------

    [Fact]
    public void Device_kernels_agree_with_the_cpu()
    {
        var rng = new Random(3);
        Tensor<float> Rand(params int[] shape) => new(Enumerable.Range(0, shape.Aggregate(1, (a, b) => a * b)).Select(_ => (float)(rng.NextDouble() * 4 - 2)).ToArray(), shape);
        var (a, b, c, bias) = (Rand(64, 32), Rand(32, 16), Rand(64, 32), Rand(32));
        var saved = DeviceOps.MinWork;
        DeviceOps.MinWork = 0;
        try
        {
            void Same(Tensor<float> cpu, Tensor<float> dev, string what)
            {
                Check.Equal(cpu.Shape, dev.Shape);
                for (var i = 0; i < cpu.Data.Length; i++)
                    Check.True(Math.Abs(cpu.Data[i] - dev.Data[i]) <= 1e-4f * Math.Max(1f, Math.Abs(cpu.Data[i])), $"{what}[{i}]: cpu {cpu.Data[i]}, device {dev.Data[i]} on {DeviceOps.DeviceName}");
            }
            Same(TensorOps.MatMul(a, b), DeviceOps.MatMul(a, b), "matmul");
            Same(TensorOps.Add(a, c), DeviceOps.Add(a, c), "add");
            Same(TensorOps.Mul(a, c), DeviceOps.Mul(a, c), "mul");
            Same(TensorOps.AddBias(a, bias), DeviceOps.AddBias(a, bias), "add_bias");
            Same(TensorOps.Relu(a), DeviceOps.Relu(a), "relu");
            Same(TensorOps.Sigmoid(a), DeviceOps.Sigmoid(a), "sigmoid");
            Same(TensorOps.Tanh(a), DeviceOps.Tanh(a), "tanh");
            Same(TensorOps.Scale(a, 0.25), DeviceOps.Scale(a, 0.25), "scale");
            Same(TensorOps.Transpose(a), DeviceOps.Transpose(a), "transpose");
            Same(TensorOps.TanhGrad(a, c), DeviceOps.TanhGrad(a, c), "tanh_grad");
        }
        finally
        {
            DeviceOps.MinWork = saved;
        }
    }

    // ---------- tools ----------

    public static IEnumerable<object[]> Samples() =>
        Directory.GetFiles(Path.Combine(Root, "samples"), "*.vs", SearchOption.AllDirectories)
                 .Select(f => new object[] { Path.GetRelativePath(Path.Combine(Root, "samples"), f) });

    [Theory]
    [MemberData(nameof(Samples))]
    public void Samples_are_in_canonical_form(string sample)
    {
        var source = File.ReadAllText(Path.Combine(Root, "samples", sample)).Replace("\r\n", "\n");
        Check.Equal(source, Formatter.Format(source));
    }

    private const string Messy = """
        // header comment
        module   Messy
        // about f
        fn f(x:Int,y:Int)->Int requires x>=0&&y>=0 ensures result>=x {   // trailing on the signature
          // before the let
          let s=x+y


          if s>3 {return s} else {return x}
        }
        fn g(a: Array[Int]) -> Int requires len(a) > 0 { return a[0] } // after g
        fn h = grad k wrt v
        fn k(v: Float) -> Float { return (v + 1.0) * -v }
        // the end
        """;

    [Fact]
    public void Formatter_produces_the_canonical_layout_and_keeps_every_comment()
    {
        const string expected = """
            // header comment
            module Messy

            // about f
            fn f(x: Int, y: Int) -> Int
              requires x >= 0 && y >= 0
              ensures result >= x
            { // trailing on the signature
              // before the let
              let s = x + y

              if s > 3 { return s }
              else { return x }
            }

            fn g(a: Array[Int]) -> Int
              requires len(a) > 0
            {
              return a[0]
            } // after g

            fn h = grad k wrt v

            fn k(v: Float) -> Float {
              return (v + 1.0) * -v
            }
            // the end

            """;
        var once = Formatter.Format(Messy);
        Check.Equal(expected.Replace("\r\n", "\n"), once);
        Check.Equal(once, Formatter.Format(once));
        Check.True(Compilation.Check(once, "messy.vs").Ok);
    }

    [Fact]
    public void Signatures_show_contracts_without_bodies()
    {
        var sig = Formatter.Signatures(File.ReadAllText(Path.Combine(Root, "samples", "types.vs")));
        Check.Contains("fn countdown(n: Nat) -> Array[Int]\n  ensures len(result) == n\n", sig);
        Check.Contains("type Shape = | Circle(r: Nat) | Rect(w: Nat, h: Nat) | Empty", sig);
        Check.DoesNotContain("  return ", sig);
        Check.DoesNotContain("  while ", sig);
    }
}
