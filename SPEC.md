# V#

V# is a .NET language designed around three goals:

1. **AI models write and repair it reliably.** The syntax has one way to say each thing, every function can be understood from its signature alone, and the compiler answers in structured data a model can act on.
2. **Programs are proved correct at compile time.** Contracts, termination, array bounds, division, refinement types and (in total mode) integer overflow are discharged by an SMT solver. A program that compiles has no unproved obligation.
3. **It is a language for building AI models.** Tensor shapes and element types are part of the type, gradients are derived by the compiler, and tensor code can run on a GPU.

It compiles to IL. A V# module is an ordinary .NET assembly that C# can reference and call.

This document describes the language as implemented by `vsharpc`. [Section 10](#10-implementation-status) lists the known limits.

```
fn binary_search(a: Array[Int], key: Int) -> Int
  requires forall i in 0..len(a) : forall j in i..len(a) : a[i] <= a[j]
  ensures -1 <= result && result < len(a)
  ensures result >= 0 ==> a[result] == key
  ensures result < 0 ==> forall k in 0..len(a) : a[k] != key
{
  var lo = 0
  var hi = len(a)
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= len(a)
    invariant forall k in 0..lo : a[k] < key
    invariant forall k in hi..len(a) : a[k] > key
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2
    if a[mid] < key { set lo = mid + 1 }
    else if a[mid] > key { set hi = mid }
    else { return mid }
  }
  return -1
}
```

`vsharpc` proves this function correct for every array and key, and compiles it to a static method `long binary_search(long[], long)`.

---

## 1. Design principles

Each feature was chosen because it serves at least two of the three goals.

| Rule | For AI authorship | For verification |
|---|---|---|
| Every statement starts with a keyword (`let`, `var`, `ghost`, `set`, `if`, `while`, `for`, `match`, `return`, `break`, `continue`, `assert`, `print`, `do`) | No statement/expression ambiguity; no semicolons or indentation to get wrong; an error is local to one statement | The parser never guesses, so the verified program is the one that was written |
| Names are unique within a function; no shadowing | A name means one thing wherever it appears in the function | Variables map one-to-one to logical symbols |
| No overloading, no implicit broadcasting, and one implicit conversion only (a class value to an interface it implements) | The call that is written is the call that runs | No hidden coercions for the proof to model |
| Named arguments are required when two parameters have the same type | Swapped arguments, the commonest silent bug in generated code, cannot compile | The call site states which value is which |
| Values only: arrays, tensors, records, classes and unions are immutable; mutation is confined to local `var`s | No action at a distance | No aliasing, so no frame conditions or separation logic, and a class invariant proved at construction holds forever |
| No `null`: absence is `Option[T]`, failure is `Result[T, E]`, and `match` must be exhaustive | Every case is handled where the value is used | Every case is a path the verifier explores |
| Functions are pure unless they declare `effects` | A signature states everything a function can do | Pure functions are mathematical functions and can appear in specifications |
| Every function has a contract and is verified against it alone (modular) | A model can edit a function with only the callees' signatures in context (`vsharpc sig`) | Proof cost grows with function size, not program size |
| Every `while` loop and recursion has a `decreases` measure, and `for` loops are bounded; all code terminates | No hangs to debug | Contracts of recursive functions are sound to assume |
| Arithmetic traps on overflow, or is proved not to overflow (total mode) | No silent wraparound | Unbounded integers are a sound model of `Int` |
| Diagnostics are data: stable code, span, counterexample, hint, and for holes the facts and obligations | The repair loop needs no prose parsing | Failures are concrete, not "could not prove" |
| One canonical layout (`vsharpc fmt`) | Diffs contain only real changes; there is no style to imitate | — |

The intended workflow follows from this: **a person (or a planning model) writes or reviews the contract; a model writes the body, using typed holes to ask what is needed; the verifier decides whether it is done.** The contract is short and is the part worth human attention.

---

## 2. Syntax

### 2.1 Grammar

```
module    := 'module' Ident 'total'? (use | decl)*  -- one file; a module may span several files
use       := 'use' dotted                           -- a .NET namespace for attribute names
decl      := attr* (typedecl | class | interface | exception | fn) | const
const     := 'const' Ident ':' type '=' expr
exception := 'exception' Ident ('(' fields? ')')? | 'exception' Ident 'from' String   -- own, or a .NET type
attr      := '@' dotted ('(' args? ')')?            -- a .NET attribute
dotted    := Ident ('.' Ident)*

typedecl  := 'type' Ident tparams? '=' ( '{' fields? '}'                      -- record
                                       | ('|' Ident ('(' fields? ')')?)+      -- union
                                       | type 'where' expr )                  -- refinement
tparams   := '[' Ident (',' Ident)* ']'
fields    := field (',' field)*          field := attr* Ident ':' type

class     := 'class' Ident '(' fields? ')' ('implements' Ident (',' Ident)*)?
               '{' ('invariant' expr)* method* '}'
method    := attr* 'fn' Ident '(' 'self' (',' params)? ')' '->' type clause* block
           | attr* 'spec' 'fn' Ident '(' 'self' (',' params)? ')' '->' type clause* '{' expr '}'
interface := 'interface' Ident '{' (attr* 'fn' Ident '(' 'self' (',' params)? ')' '->' type clause*)* '}'

fn        := 'fn' Ident generics? '(' params? ')' '->' type clause* block
           | 'fn' Ident '=' 'grad' Ident 'wrt' Ident
           | 'spec' 'fn' Ident generics? '(' params? ')' '->' type clause* '{' expr '}'
           | 'lemma' 'fn' Ident generics? '(' params? ')' ('->' 'Unit')? clause* block
           | 'extern' 'fn' Ident '(' params? ')' '->' type clause* 'from' String
generics  := '[' Ident (',' Ident)* ']'           -- type and dimension parameters, told apart by use
params    := param (',' param)*          param := attr* Ident ':' type
clause    := 'requires' expr | 'ensures' expr | 'decreases' expr (',' expr)*
           | 'effects' ('io' | 'device' | 'async') (',' ...)* | 'total'
           | 'throws' Ident ('when' expr)?

type      := 'Int' | 'Int32' | 'Bool' | 'Unit' | 'Float' | 'Decimal' | 'String' | 'Date'
           | 'Array' '[' type ']' | 'Map' '[' type ',' type ']' | 'Set' '[' type ']'
           | 'Tensor' '[' (('Float32' | 'Float64') ';')? (dim (',' dim)*)? ']'
           | Ident ('[' type (',' type)* ']')?
dim       := dterm ('+' dterm)*      dterm := datom ('*' datom)*      datom := IntLit | Ident | '(' dim ')'

block     := '{' stmt* '}'
stmt      := 'ghost'? ('let' | 'var') Ident (':' type)? '=' value
           | 'set' Ident '=' value
           | 'if' expr block ('else' (block | if-stmt))?
           | 'while' expr ('invariant' expr | 'decreases' expr (',' expr)*)* block
           | 'for' Ident 'in' sum '..' sum ('invariant' expr)* block              -- counts lo..hi-1
           | 'for' Ident (',' Ident)? 'in' sum ('invariant' expr)* block          -- elements, with index
           | 'match' expr '{' (pattern block)* '}'
           | 'return' value | 'assert' expr | 'print' expr | 'do' ('await'? call) | 'break' | 'continue'
           | 'throw' Ident ('(' args? ')')?
           | 'try' block ('catch' Ident ('(' binder (',' binder)* ')')? block)+     binder := Ident | '_'
value     := expr | 'await' call                   -- 'await' only as a whole statement value
pattern   := alt ('|' alt)*
alt       := '_' | literal | Ident ('(' Ident (',' Ident)* ')')?
literal   := '-'? IntLit | '-'? DecLit | StrLit | 'true' | 'false'

expr      := or ('==>' expr)?                      -- right associative
or        := and ('||' and)*
and       := cmp ('&&' cmp)*
cmp       := sum (('==' | '!=' | '<' | '<=' | '>' | '>=') sum)?     -- not chainable
sum       := term (('+' | '-') term)*
term      := unary (('*' | '/' | '%') unary)*
unary     := ('-' | '!') unary
           | primary ('[' expr ']' | '.' Ident | '.' Ident '(' args? ')'                -- field, method call
                      | 'with' '{' Ident ':' expr (',' Ident ':' expr)* '}')*
primary   := IntLit | FloatLit | DecLit | StrLit | 'true' | 'false' | '()' | 'result' | 'self' | '?' Ident
           | Ident '=>' expr | '(' Ident (',' Ident)* ')' '=>' expr                 -- lambda, builtin arguments only
           | Ident | Ident ('[' dims ']')? '(' args? ')'  | '(' expr ')' | '[' (expr (',' expr)*)? ']'
           | 'if' expr 'then' expr 'else' expr
           | 'match' expr '{' pattern '=>' expr (',' pattern '=>' expr)* ','? '}'
           | ('forall' | 'exists') Ident 'in' sum '..' sum ':' expr                 -- bounded
           | ('forall' | 'exists') Ident 'in' 'elems' '(' expr ')' ':' expr         -- tensor elements
           | ('forall' | 'exists') Ident ':' type (',' Ident ':' type)*
                 ('trigger' unary (',' unary)*)+ ':' expr                           -- unbounded
           | 'tensor' '[' (('Float32' | 'Float64') ';')? IntLit,* ']' '(' '-'? Number,+ ')'
args      := arg (',' arg)*        arg := (Ident ':')? expr
```

Comments are `//` to end of line. Whitespace, including newlines, is insignificant. `total`, `grad`, `wrt`, `from`, `trigger`, `use`, `class`, `interface`, `implements`, `await`, `exception`, `throws`, `when`, `throw`, `try` and `catch` are contextual: they are keywords only where the grammar expects them, so `grad` remains usable as a variable name.

`DecLit` is a decimal literal with an `m` suffix (`12.50m`); its scale is kept, as in C#. `StrLit` is double-quoted with the escapes `\" \\ \n \t \r \0 \{ \}`, and `{expr}` inside it interpolates any value through `to_str`: `"{name} owes {fee}"`. An interpolated expression cannot itself contain a string literal or a brace. An integer literal takes the type its context expects (`Int`, `Int32` or `Decimal`).

**Multi-file modules.** `vsharpc check a.vs b.vs` or `vsharpc check dir/` compiles every file as one module. Each file starts with the same `module Name` line (`TN2022`); `total` on that line applies to that file's functions. Declarations are visible across files, and diagnostics name the file they occur in.

### 2.2 Why it looks like this

- **Keyword-led statements.** Because no statement begins with an identifier or operator, the grammar is unambiguous without terminators, and a malformed statement cannot swallow its neighbours. Assignment is `set x = e`, which also keeps `=` from being confused with `==`.
- **Two conditional forms, distinguished by their second keyword.** `if c { ... }` is a statement; `if c then a else b` is an expression. The same holds for `match`: arms with blocks are statements, arms with `=>` are expressions.
- **Comparisons do not chain.** `a <= b <= c` is a syntax error with a hint to write `a <= b && b <= c`.
- **`return` always takes a value.** A `Unit` function returns `()` or falls off the end.
- **No user-defined operators and no operator overloading.** Tensor arithmetic uses named functions (`matmul`, `add`), so shapes are checked at a named call site.
- **Lambdas exist only as arguments of collection builtins** (`filter(xs, x => x > 10)`; `TN2023`). They are inlined as loops, so there are no closures, no function values and no higher-order contracts for the verifier to reason about. Each builtin has a fixed, exact (or partial, where noted) specification instead.
- **`for` needs no `decreases`.** It counts up to a bound fixed on entry, so it always terminates. `break` and `continue` apply to the innermost `for` or `while` (`TN2024`).
- **Generic parameters are not annotated with their kind.** In `fn dense[B, I, O, T](...)`, a name used inside a `Tensor[...]` shape is a dimension parameter; any other is a type parameter. Using one name as both is an error.

---

## 3. Types and values

| Type | Meaning | CLR type |
|---|---|---|
| `Int` | Integer. Proofs treat it as unbounded; at run time it is 64-bit and overflow traps (or is proved impossible in total mode). | `long` |
| `Int32` | 32-bit integer, for .NET signatures and data. Arithmetic traps on overflow like `Int`; `to_int` widens, `to_int32` narrows (proved in range). | `int` |
| `Float` | IEEE 754 binary64, including NaN, infinities and signed zeros | `double` |
| `Decimal` | .NET decimal, for money and quantities | `decimal` |
| `String` | Immutable text, compared ordinally | `string` |
| `Date` | A calendar day from 0001-01-01 to 9999-12-31 | `DateOnly` |
| `Bool` | `true` or `false` | `bool` |
| `Unit` | The single value `()` | `void` |
| `Array[T]` | Immutable sequence | `T[]` |
| `Map[K, V]` | Immutable map; iterates in insertion order | `VSharp.Runtime.Map<K, V>`, an `IReadOnlyDictionary<K, V>` |
| `Set[T]` | Immutable set; iterates in insertion order | `VSharp.Runtime.Set<T>`, an `IReadOnlyCollection<T>` |
| `Tensor[E; d1, ..., dn]` | Immutable dense tensor with element type `Float32` (the default) or `Float64` | `VSharp.Runtime.Tensor<float>` / `Tensor<double>` |
| `type P = { x: Int, y: Int }` | Record | `public sealed class P` with a constructor, get-only properties named after the fields, and structural `Equals`, `GetHashCode` and `ToString`, so it serializes with System.Text.Json as is |
| `type S = \| A(r: Int) \| B` | Tagged union | `public abstract class S` with one sealed subclass per case (`A`, `B`) |
| `type Pair[A, B] = ...`, `fn f[T](...)` | Generic types and functions | CLR generic classes and generic methods (`Pair`2`, `f<T>`) |
| `type Nat = Int where self >= 0` | Refinement type: the base type plus a predicate | The base type |
| `class C(x: Int) implements I { ... }` | Immutable record with invariants and methods ([section 3.2](#32-classes-and-interfaces)) | `public sealed class C : I`, with instance methods |
| `interface I { fn m(self) -> T ... }` | Method signatures with contracts | `public interface I` |

The prelude defines `type Option[T] = | None | Some(value: T)` and `type Result[T, E] = | Ok(value: T) | Err(error: E)`.

There is no `null`, no subtyping other than a class implementing an interface, and no implicit conversion other than from a class to such an interface: `to_float(i)` converts `Int` to `Float`, `trunc(x)` converts back (proved to be in range), and `to_f32`/`to_f64` convert tensors. `let` introduces an immutable local and `var` a mutable one; parameters are immutable. Local types are inferred; an annotation is optional and checked.

**Construction and access.** Records and cases are built by calling their name: `Point(x: 1, y: 2)`, `Some(3)`, `None`. Fields are read with `p.x`. Union values are taken apart only with `match`, which must cover every case once (or end with `_`); a missing case is a compile error (`TN2016`). Type arguments are inferred from the arguments and, failing that, from the expected type, so `first([])` has type `Option[Int]` where an `Option[Int]` is expected.

**Equality.** `==` compares numbers (`Float` by IEEE rules, so `NaN != NaN`; `Decimal` by value, so `1.0m == 1m`), `Bool`, `String` (ordinally), `Date`, and records, unions and type parameters structurally, in code and in specifications alike. Arrays, maps and sets are compared with builtins, not `==`.

**Updating records.** `p with { x: 3 }` is a copy of `p` with field `x` replaced; the other fields are unchanged, and field refinements are proved for the new value.

**Constants.** `const LIMIT: Decimal = 2m` is a module-level value built from literals, earlier constants, operators, constructors and builtins (`TN2025`). The verifier knows its value exactly.

**Arrays.** `update(a, i, v)` returns a new array; `fill(n, v)` creates one; `a[i]` reads; `len(a)` is the length. Because there is no in-place mutation, two names can never refer to storage that changes underneath one of them.

**Refinement types.** A refinement can be used anywhere a type can, except as a type argument (`Array[Nat]` is `TN2020`; write the quantifier instead). Wherever a value flows into a refined type (an argument, a return, a field, an assignment) the verifier proves the predicate (`TN3014`); wherever a refined value is read it is assumed. At public entry points the predicate is also checked at run time ([section 7](#7-compilation-to-il)).

**Integer semantics.** `+`, `-` and `*` compile to the overflow-checked IL instructions. A proof about unbounded integers therefore describes every execution that completes: the program either returns the proved result or stops with `OverflowException`; it never continues with a wrapped value. `/` truncates toward zero and `%` takes the sign of the dividend, matching IL; the verifier models exactly that, not SMT-LIB's Euclidean division.

**Total mode.** `module M total`, `fn f(...) -> T total`, or `vsharpc --total` additionally prove that every `Int` operation stays within 64 bits (`TN3011`), so total code cannot trap. In exchange, the verifier may assume every `Int` input, array element, field and call result is a 64-bit value.

**Float semantics.** The verifier models `Float` exactly, in Z3's floating-point theory with round-to-nearest-even: the counterexample to a missing NaN check is `x = NaN`. Comparisons with NaN are false in code and in proofs alike.

### 3.1 Business types and builtins

These exist so that line-of-business logic (schedules, authorizations, invoices) can be written and verified without `extern`. Each builtin is modelled exactly unless the last column says otherwise; [section 4.4](#44-what-is-trusted) lists what the partial models leave out.

| Builtins | Notes | Model |
|---|---|---|
| `str_len`, `str_sub(s, start, length)`, `str_index_of`, `str_contains`, `str_starts_with`, `str_ends_with`, `+` | `str_sub` must be in bounds (`TN3007`) | Z3 string theory |
| `str_trim`, `str_upper`, `str_lower`, `str_split`, `str_join`, `str_is_blank`, `str_eq_ignore_case` | Invariant culture; `str_is_blank` is `IsNullOrWhiteSpace` | Partial: length facts only |
| `to_str(x)` | Any value; `Date` as `yyyy-MM-dd`, `Decimal` with its scale | `Int` exact, others partial |
| `parse_int`, `parse_decimal`, `parse_date(s, format)`, `parse_time(s, formats)` | Return `Option`; invariant culture; `parse_time` gives minutes since midnight | Partial: range of the result |
| `+ - * / %` and comparisons on `Decimal`; `dec_round(x, places)`; `to_decimal`, `to_int` | Rounding is half away from zero; `/` and `%` need a non-zero divisor (`TN3006`); `to_int` needs a whole value (`TN3013`) | Real arithmetic (see 4.4) |
| `date(y, m, d)`, `is_valid_date`, `add_days`, `days_between`, `day_of_week`, `year`, `month`, `day` | `date` needs a valid date and `add_days` must stay in range (`TN3015`); `day_of_week` is 0 for Sunday, as `System.DayOfWeek` | Exact calendar |
| `has_bit(mask, bit)` | Bit `0 <= bit < 63` of the two's-complement mask (`TN3007` otherwise) | Exact |
| `append`, `concat`, `map`, `filter`, `any`, `all`, `count`, `find`, `find_last`, `sum_by`, `fold` | Inlined loops | Exact |
| `min_by`, `max_by`, `sort_by`, `sort_by_desc` | Ties keep the first element; sorting is stable | `sort_by`: a sorted permutation |
| `group_by`, `to_map` | Keys in first-occurrence order; `to_map` keeps the last value per key | Partial: every key is present |
| `map_empty`, `map_put`, `map_get` (an `Option`), `map_get_or`, `map_has`, `map_remove`, `map_size`, `map_keys`, `map_values` | | Exact membership and values; key order not modelled |
| `set_empty`, `set_of`, `set_add`, `set_has`, `set_size`, `set_items` | | Exact membership; order not modelled |
| `is_some`, `is_none`, `unwrap_or` | On `Option` | Exact |

A loop over a collection is `for x in items`, `for i, x in items` or `for i in lo..hi`. Its invariants may mention the index, and the verifier knows the index's range inside the body.

### 3.2 Classes and interfaces

These exist so that a verified core can plug into .NET dependency injection and be mocked in tests. They are deliberately small: values with behaviour, not objects with identity.

```
interface Shape {
  fn area(self) -> Decimal
    ensures result > 0m
}

class Rect(width: Decimal, height: Decimal) implements Shape {
  invariant self.width > 0m
  invariant self.height > 0m

  fn area(self) -> Decimal {
    return self.width * self.height
  }

  fn scaled(self, k: Decimal) -> Rect
    requires k > 0m
  {
    return self with { width: self.width * k, height: self.height * k }
  }
}

fn total_area(shapes: Array[Shape]) -> Decimal ensures result >= 0m { ... }
```

**Classes.** A class is a record with invariants and methods. It is built, read, updated with `with` and compared with `==` exactly like a record. It is immutable, sealed and not generic. Its invariants, listed before its methods, may use `self` and are proved at every construction, by constructor call or `with` (`TN3016`). Because the value never changes afterwards, every method, every caller and every quantifier over the class may assume them. Methods take `self` first, are called as `x.m(args)`, and follow every rule of functions: contracts, effects, termination, named arguments. They cannot be generic, lemmas or externs. A method cannot be named after a field or a member of `System.Object` (`TN2004`).

**Interfaces.** An interface lists method signatures with contracts and no bodies. An interface value is opaque: nothing is known about it but what its methods' contracts say. `==` on interface values is allowed in specifications and rejected in code, and interface values cannot be map keys or set elements, because two implementations may define equality differently. An interface cannot be constructed.

**Implementing an interface.** A class names its interfaces after `implements` and has a method of the same name for each interface method, with the same parameter names, parameter types and result type (`TN2027`). The implementation inherits the interface method's contract: it is verified against the inherited `ensures` as well as its own, and assumes the inherited `requires`. It cannot add `requires`, because a caller that sees only the interface could not know them; it may add `ensures`, which callers that know the class can use; and it may only have effects the interface method declares. A class value converts implicitly to an interface it implements, wherever that interface is expected: an argument, a return value, a `let` with an annotation, an array element, a branch of `if-then-else`.

**Dispatch and termination.** A call through an interface can run any implementation, so the call graph has an edge from each interface method to every implementation. A cycle through an interface method, such as a wrapper class whose `count` calls `count` on the interface value it holds, is rejected (`TN2028`): there is no measure that every implementation would have to decrease. Recursive structures are unions with module functions and `decreases`.

### 3.3 Attributes

`@Name` or `@Name(args)` attaches a .NET attribute to a record, union, class or interface (written above it), a function or method (above it), or a field or parameter (inline before it):

```
use System.Text.Json.Serialization

@Obsolete("Use total_area")
fn area_of_two(a: Shape, b: Shape) -> Decimal { ... }

type Dto = { @JsonPropertyName("id") key: Int, @JsonIgnore internal_note: String }
```

The name is a .NET type name, found as written, under `System`, or under a namespace named by a `use` line, with or without the `Attribute` suffix. Types are looked up in the .NET runtime and in assemblies passed with `--reference` (which `vsharpc build` copies to the output). Arguments are literals, enum members (`AttributeTargets.Method`) and arrays of those; `name: value` sets a property or field. The compiler checks that the attribute exists and is unambiguous, that a constructor accepts the arguments, that its `AttributeUsage` allows the target (a field is a property in the assembly) and that a non-repeatable attribute is used once (`TN2026`). Spec functions, lemmas, externs, refinement types and constants have no .NET form and cannot have attributes.

Attributes mean nothing to the verifier. They are for serializers, validators, frameworks and tools that read the assembly.

### 3.4 Exceptions

An exception is part of a function's contract. `throws E when cond` names an exception the function may throw and the only condition under which it does; every exception is either caught or declared, and the verifier proves the conditions. A caller that rules a condition out therefore needs no `try` at all.

```
exception Overdrawn(balance: Decimal, amount: Decimal)
exception Frozen
exception BadAmount from "System.FormatException"

extern fn parse_amount(text: String) -> Decimal
  throws BadAmount
  from "System.Decimal.Parse"

fn withdraw(a: Account, amount: Decimal) -> Account
  requires amount > 0m
  ensures result.balance == a.balance - amount
  throws Frozen when a.frozen
  throws Overdrawn when !a.frozen && amount > a.balance
{
  if a.frozen { throw Frozen }
  if amount > a.balance { throw Overdrawn(balance: a.balance, amount: amount) }
  return a with { balance: a.balance - amount }
}

fn try_withdraw(a: Account, amount: Decimal) -> Result[Account, String]
  requires amount > 0m
  ensures match result { Ok(b) => b.balance == a.balance - amount, Err(e) => a.frozen || amount > a.balance }
{
  try {
    let b = withdraw(a: a, amount: amount)
    return Ok(b)
  } catch Frozen {
    return Err("account is frozen")
  } catch Overdrawn(balance, wanted) {
    return Err("cannot withdraw {wanted} from {balance}")
  }
}
```

- **Declarations.** `exception E(fields)` declares an exception with immutable fields, built like a record (`throw E(x: 1)`, or `throw E` when it has none). `exception E from "Ns.Type"` binds a .NET exception type; it has one field, `message: String`. A bound type that would also catch a run-time stop (`OverflowException`, `ContractViolationException`, `OutOfMemoryException`, `InsufficientExecutionStackException`, or a base of one, such as `System.Exception`) is rejected (`TN2030`): stops end the program and are never control flow. Throwing a bound type needs a public constructor taking the message.
- **Exceptions are not values.** They cannot be stored, passed or returned; they exist only between a `throw` (or a call) and a `catch`.
- **`throws E when cond`.** `cond` is a `Bool` specification over the parameters (and `self`), read on entry. The function promises to throw `E` only when `cond` held; it does not promise to throw it. Without `when`, `E` may be thrown on any input. A function may have several `throws` clauses, one per exception.
- **Catching.** `try { ... } catch E(a, b) { ... } catch F { ... }` runs the first catch whose exception matches. Binders are positional, one per field, `_` skips a field, and the list can be left out; binders follow the no-shadowing rule like every other name. A catch of a bound .NET type also catches the bound types derived from it. A catch body runs outside the try, so an exception thrown from it goes to the enclosing `try` or out of the function. There is no `finally`.
- **Checked routing.** Every `throw` and every call to a function that declares `throws` is routed: through the enclosing catches, innermost first, to the first that certainly catches it. If none does, the exception leaves the function, which must declare it, unless the callee's clause has a `when` condition, in which case the verifier must prove that the condition is false at the call or that the function's own clauses cover it (`TN3017`). A catch that nothing in its try block can reach, and a catch hidden by an earlier one, are errors (`TN2030`).
- **Purity.** A function with `throws` clauses is not pure: it cannot be called from specifications (`TN2006`) or lambdas (`TN2023`). Spec functions and lemmas cannot throw (`TN2030`).
- **Interfaces.** An implementation inherits its interface method's `throws` clauses, and cannot declare an exception the interface does not (`TN2027`), so a caller of the interface sees everything an implementation can throw.
- **.NET exceptions not declared.** An exception that no clause names, such as a `NullReferenceException` from a misbehaving .NET implementation, is not caught by any catch and propagates to the .NET caller like a run-time stop.

---

## 4. Contracts and verification

### 4.1 What is written

| Construct | Where | Meaning |
|---|---|---|
| `requires e` | function | The caller must establish `e`. |
| `ensures e` | function | The function establishes `e`; `result` names the return value. |
| `decreases e1, ..., en` | function, loop | Non-negative `Int`s that decrease lexicographically on each recursive call or iteration. |
| `invariant e` | loop | Holds before the first iteration and after every iteration. |
| `invariant e` | class | Holds for every value of the class; proved at construction. |
| `throws E when e` | function | `E` is thrown only if `e` held on entry ([section 3.4](#34-exceptions)). |
| `assert e` | statement | Proved at that point, then available as a fact. |
| `spec fn f(...) -> T { e }` | declaration | A mathematical definition, usable only in specifications and ghost code. |
| `lemma fn l(...) requires ... ensures ... { ghost code }` | declaration | A theorem; its body is its proof. `do l(args)` makes its `ensures` available. |
| `ghost let` / `ghost var` | statement | Proof-only state. Ghost code cannot affect executable code. |
| `extern fn f(...) -> T requires ... ensures ... from "Ns.Type.Method"` | declaration | A .NET method imported under a trusted contract. |

Specifications may use `==>`, `match` expressions, calls to pure and spec functions, and three kinds of quantifier:

- `forall k in lo..hi : e` ranges over integers `lo <= k < hi`. It needs no trigger.
- `forall e in elems(t) : p` ranges over the elements of a tensor, in the real-number model of [section 5.4](#54-value-range-contracts).
- `forall x: T, y: U trigger f(x), g(y) : p` ranges over a whole type. It needs explicit triggers: groups of calls, indexes or field accesses that together mention every bound variable (`TN2019`). The solver instantiates the quantifier only for terms that match a trigger, which keeps proofs predictable.

All three are specification-only.

### 4.2 What is proved

For every function, the verifier proves the following for all inputs satisfying `requires` and the parameters' refinements:

1. Each `ensures` holds at each `return`, and the returned value satisfies the result's refinement.
2. Each call satisfies the callee's `requires` and parameter refinements; each constructor call satisfies the field refinements.
3. Each loop invariant holds on entry and is maintained.
4. Every loop and recursion terminates.
5. No division or remainder by zero, no out-of-bounds index, no negative array length, no out-of-range `trunc`.
6. Tensor dimension equalities that the type checker could not decide syntactically, such as `B * N == B * H * W` for a `reshape` (`TN3012`).
7. In total mode, no `Int` overflow.
8. The contract itself is well defined: obligations 2, 4 and 5 are also checked inside `requires`, `ensures`, `invariant` and spec function bodies. Clauses are checked in order, each assuming the earlier ones.
9. Every construction of a class value (constructor or `with`) satisfies the class's invariants.
10. Every method that implements an interface method meets the `ensures` it inherits, assuming only the `requires` it inherits. A direct call to the implementation must satisfy the inherited `requires` too.
11. Every exception that leaves a function satisfies the `when` condition of the clause that declares it, and an exception thrown only under a `when` condition and not caught or declared cannot occur (`TN3017`). The `ensures` clauses describe normal returns only.

Lemmas are proved like functions: the body is ghost code that must establish the `ensures`, and recursive calls in it are induction hypotheses, guarded by the `decreases` measure. Spec function bodies are checked for well-definedness and termination.

If the `requires` clauses contradict each other, the function would verify vacuously; this is reported as warning `TN3009`.

### 4.3 How it is proved

Each function is executed symbolically. Every obligation becomes one SMT query asking Z3 for a state that satisfies everything known so far but violates the obligation. *Unsatisfiable* is a proof. *Satisfiable* yields a model, which is reported as the counterexample.

- **Paths are merged.** After an `if` or a `match`, the states of the branches are joined under fresh guard constants, so sequential conditionals cost linearly, not exponentially.
- **Assert, then assume.** Once an obligation is discharged it is added to what is known, so later queries reuse it instead of re-deriving it. This is sound because an undischarged obligation rejects the module.
- **Calls are modular.** A call is replaced by the callee's contract; the body is never inlined. A pure function `f` is an uninterpreted function symbol in the logic (generic functions get one symbol per instantiation), and each application `f(args)` in the code or the specification contributes the fact `requires(args) ==> ensures(args, f(args))`. The postcondition is never assumed outside the precondition.
- **Spec functions unfold one level.** Each application of a spec function also contributes `f(args) == body(args)`. Deeper unfolding happens only where the specification or a lemma mentions the deeper terms.
- **Contracts can be definitions.** `fib` in `samples/verified_math.vs` states `n >= 2 ==> result == fib(n - 1) + fib(n - 2)`; the iterative `fib_fast` is then proved to satisfy `result == fib(n)`.
- **Loops are cut by their invariants.** After the entry check, everything known about the variables the loop assigns is discarded and replaced by the invariants. A counterexample after a loop is therefore relative to the invariants: if it shows a state the real program cannot reach, the invariant is too weak.
- **Instantiation is bounded.** Function applications nested inside an instantiated contract are not expanded further, and unbounded quantifiers are instantiated only through their triggers. This makes verification less complete but predictable: there are no matching loops, and the same program gives the same answer every time.
- **Termination guards soundness.** Recursion is found from the call graph, including calls made from specifications, and each strongly connected component (a set of mutually recursive functions) must share a measure length (`TN2012`). Every call within the component must decrease the measure lexicographically. This rejects a contract such as `ensures result == bad(x) + 1`, which would otherwise be assumed and make every proof succeed.
- **User types are SMT datatypes**, generic ones as parametric datatypes, so `match` is a case split and constructor equalities are decided by the solver.
- **Interfaces are uninterpreted sorts.** A class `C` implementing `I` gets a function `up.C.I` from `C` values to `I` values, and the implicit conversion is an application of it. An interface method is a function symbol whose applications contribute the interface contract, like any call. For each implementation, an axiom ties the two together: `I.m(up.C.I(x), args) == C.m(x, args)`, instantiated only when `I.m` is applied to a converted class value. The axioms are consistent because the `up` functions can always be chosen as disjoint injections.
- **Exceptions are paths.** A `throw`, and a call whose callee declares `throws E when c`, end a path that carries the current state plus `c` (instantiated at the call). Each catch that can receive the exception starts from the join of the states of every site routed to it, with fresh values for its binders. So inside `catch Overdrawn` the verifier knows `amount > a.balance`, and after the `try` it knows the join of the normal end of the body and each catch. A site that escapes must prove `c ==> w`, where `w` is the conjunction of the `when` conditions of the function's clauses that may match it, or `!c` if no clause covers it. The fields of a caught exception are unconstrained beyond their types: the `throws` clause says when an exception happens, not what it carries.
- **Class invariants are facts about the type.** They are assumed wherever a class value appears (a parameter, a field, an element, a call result, a quantified variable) together with the contracts of the functions they apply, and proved wherever one is built. Soundness is induction over construction: values are immutable, and V# code cannot build one without the proof. .NET code that builds one is checked at run time ([section 7](#7-compilation-to-il)).

### 4.4 What is trusted

The proof is only as good as these components: the Z3 solver; the verifier's encoding of V# into SMT; the IL emitter; the `VSharp.Runtime` library; the .NET runtime; **the contracts of `extern` functions**, which are assumed, not proved; and **the real-number model of tensor elements** ([section 5.4](#54-value-range-contracts)), which describes exact arithmetic, whereas the tensors are computed in floating point. The soundness argument for assuming a recursive function's contract while verifying it is the standard one (well-founded induction on the measure) and is informal here, not mechanised.

Proofs are about total correctness modulo three run-time stops: integer overflow outside total mode, stack exhaustion and out-of-memory.

**Approximations in the business types.** These are deliberate and trusted:

- **`Decimal` is modelled as an exact real number.** .NET decimals hold 28 to 29 significant digits: a product or quotient that needs more is rounded, and a magnitude above about 7.9 × 10^28 throws `OverflowException`. A proof about `x / 3 * 3` therefore describes exact arithmetic, not the rounded result. Sums, differences and products of amounts with a few decimal places, which is what money code does, are exact in both.
- **Strings are Z3 strings**, which are sequences of Unicode code points; .NET strings are UTF-16 code units. `str_len` and indexes agree for text without surrogate pairs (characters outside the Basic Multilingual Plane, such as emoji).
- **Culture-sensitive operations are uninterpreted.** `str_trim`, `str_upper`, `str_lower`, `str_split`, `str_join`, the parse builtins and `to_str` of decimals and dates are function symbols with a few facts (lengths, ranges). The verifier never assumes more than those facts, so nothing false is proved, but properties that depend on what the functions actually compute cannot be proved. They run with the invariant culture.
- **`group_by` and `to_map` are described partially** (every input key is present). **Key order in maps and sets is not modelled.**
- **Calendar ranges.** `year`, `month` and `day` of a valid day are assumed to lie in their ranges. This is true of the exact calendar functions, but the solver cannot derive it through the calendar arithmetic in reasonable time.
- **No null.** A .NET caller must not pass `null` for a `String`, record, class, interface, array, map or set; the entry checks do not test for it. Code at the boundary maps missing values to `""` or `Option`.

**Interfaces implemented outside V#.** A C# class, a mock or a proxy can implement a V# interface, and V# code that calls it assumes the interface contract, exactly as it assumes an `extern` contract. Such an implementation is trusted to meet the `ensures`, to have no effects beyond those declared, to throw only the declared exceptions under their `when` conditions, and to terminate. An `extern` is trusted the same way: its `throws` clauses are assumed to list everything it can throw that V# code should catch. Implementations written in V# are proved.

**Class invariants at run time.** The constructor checks the invariants that run no V# function (fields, operators, builtins and bounded quantifiers), so .NET code cannot build a value that violates them. An invariant that calls a function is not checked at run time, because the function could construct the class again; .NET code that constructs such a class is trusted to respect it.

---

## 5. Tensors

### 5.1 Shapes

A tensor's shape is part of its type. Dimensions are positive integer literals, **dimension parameters** declared on the function, or sums and products of them:

```
fn dense[B, I, O](x: Tensor[B, I], w: Tensor[I, O], b: Tensor[O]) -> Tensor[B, O] {
  return add_bias(matmul(x, w), b)
}

fn flatten[B, H, W](x: Tensor[B, H, W]) -> Tensor[B, H * W] {
  return reshape[B, H * W](x)
}
```

At each call the checker solves the dimension parameters from the argument types and substitutes them into the return type. Dimension expressions are compared as polynomials, so `H * W` and `W * H` are the same dimension. When two dimensions are different polynomials (`N` and `H * W`), the checker hands the equality to the verifier, which proves it from the `requires` clauses (`TN3012`). A dimension mismatch between constants is a type error:

```
shape mismatch in argument 'w' of 'dense': expected Tensor[I, O] (with B = B, I = 3) but found Tensor[4, 2]
```

Every dimension parameter must appear on its own in some parameter type, so callers can always solve it. Inside the function a dimension parameter is also an `Int` value, usable in code and contracts (`forall i in 0..B : ...`); at run time it is read from the shape of the argument that determines it.

There is **no implicit broadcasting**. `add` requires identical shapes; adding a bias vector is the separate, named `add_bias`. Silent broadcasting is among the most common causes of ML code that runs and computes the wrong thing.

### 5.2 Builtins

| Builtin | Shape |
|---|---|
| `matmul(a, b)` | `[M, K] x [K, N] -> [M, N]` |
| `add`, `sub`, `mul` (elementwise) | `[...] x [...] -> [...]` |
| `scale(t, s: Float)`, `relu`, `tanh`, `sigmoid` | `[...] -> [...]` |
| `softmax(t)` | `[B, N] -> [B, N]`, along rows |
| `add_bias(x, b)` | `[B, N] x [N] -> [B, N]` |
| `transpose(t)` | `[M, N] -> [N, M]` |
| `reshape[d1, ..., dn](t)` | any shape with the same element count, proved |
| `full[d1, ..., dn](v: Float)` | a constant tensor |
| `sum(t) -> Float` | all elements |
| `sum_rows(t)` | `[B, N] -> [N]` |
| `to_f32(t)`, `to_f64(t)` | element type conversion |
| `relu_grad`, `tanh_grad`, `sigmoid_grad`, `softmax_grad` | the vector-Jacobian products used by `grad` |
| `tensor[E; d1, ..., dn](v, ...)` | a literal; the value count is checked against the shape |

The element type is part of the type: `Tensor[Float64; 3]` and `Tensor[3]` (`Float32`) do not mix without `to_f64`/`to_f32`.

### 5.3 Automatic differentiation

`fn d = grad f wrt p` defines `d` as the gradient of `f` with respect to its parameter `p`. `f` must return `Float`, `p` must be a `Float` or a tensor, and the result type of `d` is the type of `p`. `d` takes the same parameters as `f`.

The gradient is a compile-time source transformation (reverse mode). The compiler lowers `f` to one operation per `let`, inlining straight-line helper functions with their dimension parameters substituted. It then generates the backward pass as ordinary V# code from per-operation vector-Jacobian rules. The generated function is type-checked, shape-checked and verified like any hand-written function, so a gradient with a shape error cannot exist. `f` must be straight-line (`let`, `assert`, `return`) over `Float` arithmetic and the differentiable builtins (`TN2015` otherwise). `relu` uses the subgradient 0 at 0.

### 5.4 Value-range contracts

Tensor element facts are stated with `forall e in elems(t) : ...` and `row_sum(t, i)`, and are proved in a **real-number model**: element `i` of a tensor is a real number, and each builtin contributes its exact meaning (`add`, `sub`, `mul`, `scale`, `relu`, `add_bias`, `reshape`, `full` and the conversions) or its range (`sigmoid` and `softmax` in `[0, 1]`, `tanh` in `[-1, 1]`, each `softmax` row summing to 1). For example:

```
fn classify[B](logits: Tensor[B, 3]) -> Tensor[B, 3]
  ensures forall e in elems(result) : 0.0 <= e && e <= 1.0
  ensures forall i in 0..B : row_sum(result, i) == 1.0
{
  return softmax(logits)
}
```

The model describes the exact computation that floating-point tensors approximate; it is a stated assumption ([section 4.4](#44-what-is-trusted)), not a theorem about rounding. A false range claim, such as `relu` outputs being at most 1, is refuted.

---

## 6. Effects

A function with no `effects` clause is pure: its result depends only on its arguments, and it may appear in specifications.

| Effect | Allows |
|---|---|
| `io` | `print`, and calls to `io` functions |
| `device` | Running tensor builtins on an accelerator, and calls to `device` functions |
| `async` | `await` on calls to `async` functions |

A function must declare the effects of everything it calls. Effectful functions cannot be called from pure functions or specifications, but they are still verified and still must terminate. `main` is `fn main() -> Unit` with whatever effects it uses.

**The `async` effect.** An `async` function runs until it awaits something unfinished, then gives its thread back and continues when that finishes. In .NET it returns a `Task` (for `Unit`) or `Task<T>`, so it can call asynchronous .NET APIs and C# can await it.

```
extern fn pause(ms: Int32) -> Unit effects async from "System.Threading.Tasks.Task.Delay"

interface Source {
  fn fetch(self, key: Int) -> Int effects async
    requires key >= 0
    ensures result >= key
}

fn twice(src: Source, key: Int) -> Int effects async
  requires key >= 0
  ensures result >= key
{
  let n = await src.fetch(key)
  do await pause(1)
  return n
}
```

- Every call to an `async` function is awaited, and only such calls can be (`TN2029`). There are no task values in the language: a call either runs to completion before the next statement, or it is not written.
- `await` is the whole value of a `let`, `var`, `set`, `return` or `do` statement, never part of a larger expression (`TN2029`). Every suspension point is therefore a statement, which is what the reader, the verifier and the state machine ([section 7](#7-compilation-to-il)) all see.
- **Verification is unchanged.** An awaited call is a call: the verifier assumes the callee's `ensures` for a fresh result, as for any effectful call. Because V# values are immutable and a function's variables are its own, nothing can change them while the function is suspended, so the sequential reasoning is exact.
- An `async` function cannot be generic (`TN2013`). An interface method and its implementation agree on `async` (`TN2027`), since both return a `Task` in .NET. An `async` `main` is run to completion by the entry point.
- An `async` `extern` binds a .NET method that returns `Task` (for `Unit`) or `Task<T>` with `T` the CLR type of the declared result.

**The `device` effect.** Inside a `device` function, tensor builtins dispatch to `VSharp.Runtime.DeviceOps`. That class runs `Float32` matmul, elementwise operations, `add_bias` and `transpose` on an accelerator through ILGPU: CUDA when available, then OpenCL, then ILGPU's CPU accelerator. Operations smaller than 65,536 scalar operations stay on the host, where they are faster than a kernel launch. `VSHARP_DEVICE` selects `cuda`, `opencl`, `cpu` or `host` (no accelerator); `VSHARP_DEVICE_MIN` sets the size threshold (0 sends everything to the accelerator). `device` is an effect rather than a hidden optimisation because accelerator results may differ from CPU results in the last bits of rounding. Pure functions are always computed on the CPU and are deterministic.

---

## 7. Compilation to IL

| V# | IL |
|---|---|
| `module M` | `public abstract sealed class M` (a static class) in assembly `M.dll` |
| `fn f(x: Int) -> Int` | `public static long f(long x)` |
| `fn f[T](x: T) -> T` | `public static T f<T>(T x)` |
| Dimension parameters | Erased from signatures; read from argument shapes where used as values |
| Records, unions, cases | Classes, as in [section 3](#3-types-and-values); a generic case is `Some`1` |
| `match` | `isinst` per case, then field loads |
| `requires` / `ensures` | `[Contract(kind, text)]` attributes on the public method |
| A module whose proofs all passed | `[Verified("vsharpc")]` on the class |
| `+ - *` on `Int` / `Float` | `add.ovf`, `sub.ovf`, `mul.ovf` / `add`, `sub`, `mul` |
| `/ %` | `div`, `rem` |
| `<=`, `>=` on `Float` | `cgt.un` / `clt.un` then negate, so comparisons with NaN are false |
| `trunc`, `to_float` | `conv.ovf.i8`, `conv.r8` |
| `&& \|\| ==>`, `if-then-else` | Short-circuit branches |
| `a[i]`, `len(a)` | `ldelem`, `ldlen` |
| `extern fn` | A direct `call` to the .NET method |
| `class C(...) implements I` | `public sealed class C : I`, built like a record; its constructor checks the invariants |
| Method `fn m(self, x: T)` of a class | `public` instance method `m(T x)`; `public virtual final` when it implements an interface method |
| `interface I` and its methods | `public interface I` with abstract instance methods |
| `x.m(args)` | `call` for a class method, `callvirt` for an interface method |
| Class value where an interface is expected | Nothing: the reference is passed as is |
| `@Attr(args)` | A custom attribute on the class, interface, property, public method or parameter |
| `Int32`, `Decimal`, `String`, `Date`, `Map`, `Set` | `int`, `decimal`, `string`, `DateOnly`, `VSharp.Runtime.Map<K, V>`, `VSharp.Runtime.Set<T>` |
| Record field `x` | Private field `x$` and public get-only property `x`; structural `Equals`, `GetHashCode`, `ToString` |
| `for`, `break`, `continue` | Branches; an array loop reads the length once |
| `map`, `filter`, `fold` and the other lambda builtins | Inlined loops; sorting and grouping compute a key array, then call `VSharp.Runtime.Rt` |
| `const` | Inlined: each use evaluates the constant's expression in place |
| `update`, `fill`, tensor operations, `print` | Calls into `VSharp.Runtime` (`TensorOps`, or `DeviceOps` in `device` functions) |
| `assert`, `invariant`, `decreases`, quantifiers, ghost statements, lemma calls | Nothing: proved, then erased |
| `spec fn`, `lemma fn` | Nothing |
| `fn main` | The assembly's entry point; for an `async` `main`, a `main$entry` that waits for its task |
| `fn f(x: Int) -> Int effects async` | `public static Task<long> f(long x)` (`Task` for `Unit`); the body moves into a state machine class `f$async` |
| `let v = await g(...)` | Call `g`; if its task is unfinished, save the IL locals into machine fields, record the resume point, schedule the machine with `ConfigureAwait(false)` and return. On resumption, restore the locals, then read the result |
| `exception E(x: T)` | `public sealed class E : System.Exception` with field `x$`, property `x` and a public constructor; `Message` is `E(x: ...)` |
| `exception E from "Ns.T"` | The .NET type itself; `throw E(m)` calls its `(string)` constructor |
| `throw E(args)` | `newobj`, then `throw` |
| `try { } catch E(a) { }` | A protected region with one typed handler per catch; the handler only stores the exception and `leave`s, and the catch body runs after the region. `return`, `break` and `continue` inside the region become `leave` |
| `throws E when e` | `[Contract("throws", "E when e")]` on the public method |

**Entry checks.** V# callers have proved every precondition, but a C# caller has not. A function whose `requires` clauses or refined parameters can be evaluated at run time is therefore compiled twice. An internal `f$impl` holds the body, and V# code calls it directly at no cost. A public `f` checks the preconditions, including those a method inherits from its interface, and the refinements, throws `VSharp.Runtime.ContractViolationException` naming the violated clause, and otherwise calls `f$impl`. Bounded quantifiers are compiled to loops for these checks. A clause that cannot run (an unbounded quantifier, a spec function) is recorded as `[Contract("requires-unchecked", ...)]`. A class constructor likewise checks the invariants that run no V# function ([section 4.4](#44-what-is-trusted)). `--no-entry-checks` turns the wrappers and the constructor checks off. An `async` function's entry checks run before its task is created, so a violated precondition throws synchronously; an exception raised after that, including from an awaited .NET task, faults the returned task.

**Async state machines.** `f` creates an instance of `f$async` (derived from `VSharp.Runtime.AsyncMachine`), copies its arguments into fields and starts it through `VSharp.Runtime.Async`, which owns the `TaskCompletionSource` and turns exceptions into a faulted task. The machine's `Run` method holds the body, with a jump table on a state field that selects the start or the point after an `await`. Continuations run without the caller's synchronization context. IL cannot jump into a protected region, so a `try` that contains an `await` starts with a small dispatch: on resumption, the jump table branches to the `try`'s entry, and the dispatch inside the region branches on to the resume point, through each nested `try` in turn. Suspending from inside a region `leave`s it. An exception that escapes `Run` faults the task.

**Referencing from C#.** The assembly references `System.Runtime`, as assemblies compiled by C# do, rather than `System.Private.CoreLib`, which `PersistedAssemblyBuilder` would otherwise write and which compilers cannot see. A C# project can therefore reference `M.dll` directly and call `M.f(...)`, construct records with `new P(...)` and options with `new Some<int>(5)` or `new None<int>()`, read fields as properties, register a V# class as the implementation of a V# interface in a dependency-injection container, and mock the interface in tests.

`vsharpc build` refuses to emit an assembly with a failed obligation. `--no-verify` emits one without the `[Verified]` attribute. The output directory receives `M.dll`, its `runtimeconfig.json`, `VSharp.Runtime.dll` and the ILGPU libraries.

---

## 8. Tools for AI authorship

**Typed holes.** `?name` stands for an expression still to be written. Compilation stops with `TN4001`, which reports the hole's type, the variables in scope, the facts known at that point and the obligations the missing expression must meet:

```
hole.vs(9,10): error TN4001: hole ?answer has type Int
  in scope: a: Int, b: Int
  known: !(a > b)
  must satisfy: postcondition of 'max' might not hold: result >= a && result >= b
  hint: Replace the hole with an expression of this type that meets the obligations listed.
```

**Named arguments.** When two or more parameters of a user function or constructor have the same type, every call must name all its arguments, in declaration order: `clamp(x: 150, lo: 0, hi: 100)` (`TN2014`). Names are allowed, in order, on any call to a user function.

**Canonical formatter.** `vsharpc fmt` prints the one layout of a program, which is a function of its syntax tree and comments alone. Formatting is idempotent and preserves every comment. Its rules:

- Two-space indentation.
- Contract clauses one per line.
- Effects on the signature line.
- `if c { s }` and `Pattern { s }` on one line when every branch is a single simple statement and the line fits in 100 characters.
- At most one blank line in a row.
- Tensor literals one row per line.
- Calls and array literals longer than 80 characters one element per line, aligned after the bracket.
- A chain of `&&` or `||` longer than 80 characters one operand per line, the operator first.
- Record types and class headers longer than 100 characters one field per line.
- `use` lines together after the module line; attributes of a declaration one per line above it, of a field or parameter inline.
- In a class, invariants first, then methods separated by blank lines.

`--check` exits 1 when a file is not canonical; `--write` rewrites it.

**Signatures.** `vsharpc sig` prints a module's types, signatures, contracts and spec function bodies without executable bodies: everything a caller can rely on, at a fraction of the size.

**Explanations.** `vsharpc explain` lists every diagnostic code; `vsharpc explain TN2014` prints its explanation and an example fix. `--json` gives both as data.

---

## 9. Using it

```
dotnet build
dotnet run --project src/VSharp.Compiler -- run samples/train.vs
```

| Command | Effect |
|---|---|
| `vsharpc check <files>` | Parse, type-check and verify. Exit code 1 on any error. |
| `vsharpc build <files> [-o dir]` | Check, then write `<Module>.dll` to `dir` (default `./out`). |
| `vsharpc run <files> [-o dir]` | Build, then run `main`. |
| `vsharpc fmt <files> [--write \| --check]` | Canonical layout, file by file. |
| `vsharpc sig <files> [--json]` | The module's interface. |
| `<files>` | One or more `.vs` files or directories (every `.vs` file in a directory, in name order), all in one module. |
| `vsharpc explain [<code>] [--json]` | Diagnostic explanations. |
| `--json` | Print the result as JSON on stdout. |
| `--timeout <ms>` | Solver limit per obligation (default 5000). |
| `--emit-smt <dir>` | Write every solver query as an SMT-LIB file. |
| `--no-verify` | Skip verification; the assembly is not marked `[Verified]`. |
| `--total` | Verify every function in total mode. |
| `--no-entry-checks` | Do not generate run-time precondition and class-invariant checks. |
| `--reference <dll>`, `-r <dll>` | Look up attribute types in this assembly too (repeatable); `build` and `run` copy it to the output directory. |

| Sample | Shows |
|---|---|
| `verified_math.vs` | Contracts, recursion, contracts as definitions |
| `search.vs` | Loops, invariants, quantifiers, arrays |
| `types.vs` | Records, unions, `Option`, `Result`, generics, `match`, refinement types, entry checks |
| `proofs.vs` | `spec fn`, `lemma fn`, ghost variables, mutual recursion, lexicographic measures, triggers |
| `total.vs` | Total mode |
| `floats.vs` | `Float`, NaN, `extern fn` binding `System.Math.Sqrt`, `trunc` |
| `mlp.vs` | Tensor shapes and dimension parameters |
| `train.vs` | `grad`, a training loop with `effects device`, value-range contracts |
| `business.vs` | Strings, decimals, dates, collection builtins, maps, `for`, `with`, literal patterns, records as DTOs |
| `shapes.vs` | Interfaces with contracts, classes with invariants and methods, dispatch, attributes (`JsonPropertyName`, `Description`, `Obsolete`) |
| `async.vs` | `async` functions, an async interface method and its implementation, `await` in loops and `match` arms, an `async` `extern` binding `Task.Delay`, an `async` `main` |
| `exceptions.vs` | Exceptions with `throws ... when` conditions, a guarded call that needs no `try`, catch-precise `ensures`, propagation, `break`/`continue` across `try`, a bound .NET exception (`FormatException` from `Decimal.Parse`), an interface method that throws, `await` inside `try` and `catch` |
| `scheduling/` | A three-file module porting recurrence, appointment-status and authorization-limit logic |

### Diagnostics

Every diagnostic has a stable code, a source span and, where one applies, a hint. A refuted obligation has `"status": "refuted"` and a counterexample giving the value of each variable in scope; `"status": "unknown"` means the solver could not decide, usually because it hit its time limit. Both are errors: nothing unproved compiles.

```json
{
  "code": "TN3001",
  "severity": "error",
  "message": "postcondition of 'abs' might not hold: result >= 0",
  "file": "postcondition.vs",
  "line": 7, "col": 14, "endLine": 7, "endCol": 22,
  "hint": "Either the code returns a wrong value on this path, or the 'ensures' clause is too strong. The counterexample gives concrete inputs.",
  "status": "refuted",
  "counterexample": { "x": "-1", "result": "-1" }
}
```

| Code | Meaning |
|---|---|
| `TN1001` | Syntax error |
| `TN2001` | Unknown name |
| `TN2002` | Type mismatch |
| `TN2003` | Tensor shape mismatch |
| `TN2004` | Name already used (no shadowing or redefinition) |
| `TN2005` | Assignment to an immutable variable |
| `TN2006` | Effect used without being declared |
| `TN2007` | Wrong number of arguments |
| `TN2008` | Specification-only construct in executable code |
| `TN2009` | Unknown or invalid tensor dimension |
| `TN2010` | Missing `return` |
| `TN2011` | Missing `decreases` on a loop or recursive function |
| `TN2012` | Mutually recursive functions with measures of different lengths |
| `TN2013` | Other structural error |
| `TN2014` | Named arguments required |
| `TN2015` | Cannot differentiate |
| `TN2016` | Invalid or non-exhaustive `match` |
| `TN2017` | Invalid `extern` |
| `TN2018` | Ghost code misuse |
| `TN2019` | Missing or invalid trigger |
| `TN2020` | Refinement type used as a type argument |
| `TN2021` | Cannot infer a type |
| `TN2022` | Files of one module declare different module names |
| `TN2023` | Lambda outside a collection builtin, or with the wrong number of parameters |
| `TN2024` | `break` or `continue` outside a loop |
| `TN2025` | Invalid constant |
| `TN2026` | Invalid attribute |
| `TN2027` | Invalid interface implementation |
| `TN2028` | Recursion through an interface method |
| `TN2029` | Async call not awaited, `await` on a call that is not async, or `await` inside an expression |
| `TN2030` | Exception neither caught nor declared, unreachable or hidden catch, throwing spec function or lemma, or an invalid .NET exception binding |
| `TN3001` | Postcondition might not hold |
| `TN3002` | Precondition of a callee might not hold |
| `TN3003` | Assertion might not hold |
| `TN3004` | Loop invariant might not hold on entry |
| `TN3005` | Loop invariant might not be maintained |
| `TN3006` | Possible division by zero |
| `TN3007` | Index might be out of bounds |
| `TN3008` | Loop or recursion might not terminate |
| `TN3009` | Preconditions are unsatisfiable (warning) |
| `TN3010` | Array length might be negative |
| `TN3011` | Integer overflow possible (total mode) |
| `TN3012` | Tensor dimensions might differ |
| `TN3013` | Conversion to `Int` might fail |
| `TN3014` | Refinement might not hold |
| `TN3015` | Date might be invalid or out of range |
| `TN3016` | Class invariant might not hold |
| `TN3017` | Exception might be thrown outside its `when` condition, or might escape uncaught and undeclared |
| `TN4001` | Typed hole |

### Tests

`dotnet test tests/VSharp.Tests` runs 97 tests:

- Each sample verifies, compiles and prints the expected output, and the training sample learns XOR.
- Each program in `tests/cases/fail` is rejected with exactly its expected codes. There is one case per verification and type error.
- Counterexamples really violate the contract, including a NaN counterexample.
- Typed holes report their scope, facts and obligations.
- Every diagnostic code the compiler can emit has an explanation.
- The emitted assembly is callable through reflection, carries its contracts, traps on overflow, and checks preconditions and refinements at public entry points.
- Unions and generics are ordinary CLR types, and ghost code and spec functions are absent from the IL.
- Generated gradients match central finite differences.
- Device kernels agree with the CPU implementation.
- Every sample is in canonical form, and formatting is idempotent and keeps every comment.
- Records are DTOs: properties, structural equality, and System.Text.Json serialization.
- A module can span several files, diagnostics name the right file, and the scheduling module verifies and references `System.Runtime`.
- Interfaces are CLR interfaces and classes implement them; a `DispatchProxy` mock of a V# interface can be passed to V# code; constructors reject invariant violations and methods check inherited preconditions.
- Invariants that call spec functions and inherited contracts are usable in proofs, and a direct call to an implementation must meet the inherited `requires`.
- Attributes reach the emitted members (System.Text.Json honours `JsonPropertyName`), including attribute types from a `--reference` assembly.
- Async functions and interface methods return `Task<T>`; C# awaits them, a `DispatchProxy` implementation mixing finished and delayed tasks drives the suspend-and-resume path, a faulted .NET task faults the V# task, and a violated precondition throws before any task exists.
- Exceptions are sealed CLR classes derived from `System.Exception` with properties and a readable `Message`; C# catches them from V# calls and from faulted V# tasks; methods carry their `throws` contracts; and V# code catches an exception thrown by a `DispatchProxy` implementation of a V# interface.

---

## 10. Implementation status

The compiler is in `src/VSharp.Compiler`, the runtime library in `src/VSharp.Runtime`. It targets .NET 10. It uses `PersistedAssemblyBuilder` to write IL, Z3 (NuGet package `Microsoft.Z3`) to prove obligations, and ILGPU for the `device` effect. Everything in sections 2 to 8 is implemented. The known limits are:

- **Verification is incomplete by design.** Bounded instantiation and one-level unfolding mean some true properties need an intermediate `assert`, a lemma or a stronger invariant. Exact IEEE reasoning about products is expensive, so a range fact about `x * y` can time out where a cheap guard (`if p < 0.0 || p > 100.0 { ... }`) makes it unnecessary.
- **`grad`** handles straight-line code over `Float` and the differentiable builtins, not loops or branches, and not generic functions.
- **Types.** Float literals have no exponent notation. Tensor fields of records must have literal dimensions. Refinements cannot be type arguments. There is no time-of-day or date-time type: times are `Int` minutes or ticks, as the scheduling port does.
- **Classes and interfaces** are not generic, classes are sealed and immutable, and there is no inheritance between classes or between interfaces. Recursion through an interface method is rejected rather than proved. Attribute arguments are limited to literals, enum members and arrays (no `typeof`), and attributes cannot be placed on the module class or the assembly.
- **Async** is sequential: there is no `Task.WhenAll`-style concurrency, no cancellation token, no generic async function, and `await` is a statement, not an expression. Concurrency belongs in the C# shell, which can start several V# tasks and await them together.
- **Exceptions** have no `finally` and no rethrow-as-is, are not values, and cannot be generic. A `when` condition reads only the parameters, so "thrown when the lookup fails" must be phrased through a spec function of the inputs. The verifier knows when an exception was thrown, not what its fields hold. Bound .NET exceptions carry only their message.
- **Not in the language, by design.** Mutable objects and class inheritance stay in C#. The intended split is a thin C# shell (controllers, data access, logging, dependency-injection setup) around a verified V# core of decisions; V# interfaces and classes are the seams between the two.
- **`extern`** binds static methods and properties whose signatures use only `Int`, `Int32`, `Float`, `Bool`, `String`, `Decimal`, `Date`, `Unit` and arrays of those, or, for an `async` extern, a `Task` of one of them.
- **`device`** accelerates `Float32` matmul, elementwise operations, `add_bias` and `transpose`; `softmax`, reductions and `Float64` work run on the host.
