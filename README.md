# V#

V# is a .NET language an agent can write, and a compiler that decides when the agent is done.

A person writes the contract. An agent writes the body. `vsharpc` proves the body meets the contract for every input, or returns the input that breaks it. A module that compiles is an ordinary .NET assembly. C# calls it like any other library.

In identifiers, where `#` is not allowed, the name is VSharp: `VSharp.Compiler`, `VSharp.Runtime`. Source files are `.vs`.

## The loop

This is the whole workflow.

1. **State the contract.** `requires` is what the caller must guarantee. `ensures` is what the function guarantees back. `result` names the return value. The contract is short, and it is the part worth a person's attention.
2. **Let the agent write the body.** It can leave `?name` where an expression is still missing. The compiler answers with the hole's type, the names in scope, the facts known there, and the obligations the expression must meet.
3. **Ask the compiler.** `vsharpc check --json` either accepts the module or returns a diagnostic: a stable code, a source span, a hint, and, when the solver found one, a counterexample.
4. **Repair from the counterexample.** The agent edits the body, or the contract if the contract was wrong, and checks again. Nothing unproved compiles, so "done" is a compiler result.

```
fn discounted(price: Decimal, percent: Decimal) -> Decimal
  requires price >= 0m
  ensures 0m <= result && result <= price
{
  return price - price * percent / 100m
}
```

```json
{
  "code": "TN3001",
  "message": "postcondition of 'discounted' might not hold: 0m <= result && result <= price",
  "status": "refuted",
  "counterexample": { "price": "1m", "percent": "101m", "result": "-0.01m" },
  "hint": "Either the code returns a wrong value on this path, or the 'ensures' clause is too strong. The counterexample gives concrete inputs."
}
```

A 101% discount makes the price negative. The fix is a precondition, `requires 0m <= percent && percent <= 100m`, which the verifier then demands of every caller. Changing a contract flags exactly the call sites that no longer hold. Changing a body re-proves only that function.

## What an agent needs in context

Verification is modular. A call is replaced by the callee's contract, so the callee's body is not part of the proof and does not need to be in the prompt.

| Command | What the agent gets |
|---|---|
| `vsharpc sig` | Every type, signature, and contract in the module, with no executable bodies. This is the context for writing a caller. |
| `vsharpc check --json` | `{ ok, verified, queries, output, diagnostics }`. Each diagnostic has `code`, `file`, `line`, `col`, `hint`, `status`, and `counterexample`. |
| `vsharpc explain TN3001` | What the code means and an example fix. `--json` returns the same as data. |
| `vsharpc fmt --check` | Fails unless the file is in the one canonical layout. `--write` rewrites it. A diff then contains only the real change. |

A typed hole is a question to the compiler:

```
fn max(a: Int, b: Int) -> Int
  ensures result >= a && result >= b
{
  return ?answer
}
```

```
error TN4001: hole ?answer has type Int
  in scope: a: Int, b: Int
  must satisfy: postcondition of 'max' might not hold: result >= a && result >= b
```

## Why generated code goes wrong less often

The syntax has one way to say each thing, chosen so a model has fewer silent mistakes available.

- **Every statement starts with a keyword** (`let`, `set`, `if`, `return`, `do`, …). There are no semicolons, and a broken line cannot swallow the next one.
- **Names are unique inside a function.** There is no shadowing, so a name means one thing everywhere it appears.
- **Arguments are named when two parameters share a type.** `discounted(price: p, percent: c)` cannot be written with the arguments swapped.
- **There is no null and no overloading.** Absence is `Option`, expected failure is `Result` or a `throws` clause, and `match` must cover every case.
- **Values do not change after they are built.** Only a local `var` is mutable, so a function cannot change data the caller still holds.
- **Effects are part of the signature.** A function that prints says `effects io`. A function that awaits says `effects async`. With no effects and no `throws`, a function is pure and may appear inside contracts.
- **Every loop and every recursion ends.** A `for` is bounded. A `while` or a recursive function states a `decreases` measure that shrinks. An agent cannot leave a hang for a test run to discover.
- **Overflow does not wrap.** `Int` arithmetic traps, or, in `total` mode, the compiler proves it cannot happen.

## Build and run

The compiler targets the .NET 10 SDK.

```
dotnet build
dotnet run --project src/VSharp.Compiler -- run samples/exceptions.vs
dotnet run --project src/VSharp.Compiler -- check examples/bank.vs --json
dotnet run --project src/VSharp.Compiler -- sig samples/business.vs
```

`check` parses, type-checks, and verifies. `build` writes `<Module>.dll` and refuses to emit it when any obligation fails. `run` builds, then runs `main`. Tests are `dotnet test VSharp.sln`.

## Read next

- [SPEC.md](SPEC.md) is the language: syntax, contracts, verification, effects, and the IL the compiler emits.
- [docs/vsharp-primer.html](docs/vsharp-primer.html) is an introduction for C# developers, built around the verifier.
- [examples/bank.md](examples/bank.md) walks through a transfer function, with the real compiler output from each wrong version.
- `samples/` is one file per feature. `samples/search.vs` is the binary search above, proved.
