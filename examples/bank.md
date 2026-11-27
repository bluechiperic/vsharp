# Walkthrough: verifying a bank transfer

This walkthrough shows how formal verification works while you write a V# application. You state what the code must guarantee, write the code, and the verifier either proves the guarantee for every possible input or shows concrete inputs that break it.

The finished program is [`bank.vs`](bank.vs). Every compiler message below is real `vsharpc` output from the intermediate versions. Line and column numbers refer to the file as it was at that step.

## Step 1: State what must be true

Money can't be negative, and a transfer must never create or destroy money:

```
module Bank

type Money = Int where self >= 0

type Account = { id: Int, balance: Money }

type Accounts = { source: Account, target: Account }

type TransferError = | InsufficientFunds(short: Int) | SameAccount

fn transfer(src: Account, dst: Account, amount: Int) -> Result[Accounts, TransferError]
  ensures match result { Ok(moved) => src.id != dst.id && moved.source.balance + moved.target.balance == src.balance + dst.balance, Err(e) => true }
```

- `Money` is a **refinement type**: an `Int` that is always at least zero. Every `Account` balance has this type, so no code anywhere may build an account with a negative balance.
- The `ensures` clause is the guarantee: a successful transfer involves two different accounts and leaves the total balance unchanged.

Because `src` and `dst` have the same type, every call must name its arguments (`transfer(src: a, dst: b, amount: 10)`). Swapping the two accounts by accident can't compile.

## Step 2: Write the obvious code and check it

```
{
  if amount > src.balance {
    return Err(InsufficientFunds(short: amount - src.balance))
  }
  let new_src = Account(id: src.id, balance: src.balance - amount)
  let new_dst = Account(id: dst.id, balance: dst.balance + amount)
  return Ok(Accounts(source: new_src, target: new_dst))
}
```

This looks fine and would pass most code reviews. `vsharpc check examples/bank.vs` rejects it with two bugs:

```
examples/bank.vs(21,46): error TN3014: field 'balance' of 'Account' might not satisfy refinement type Money: self >= 0
  counterexample: src = (Account 0 0), dst = (Account 0 0), amount = -1, new_src = (Account 0 1)
  hint: Every value of type Money must satisfy its 'where' clause.
examples/bank.vs(22,3): error TN3001: postcondition of 'transfer' might not hold: match result { ... }
  counterexample: src = (Account 4 0), dst = (Account 4 38), amount = 0, new_src = (Account 4 0), new_dst = (Account 4 38), result = (Ok (Accounts (Account 4 0) (Account 4 38)))
  hint: Either the code returns a wrong value on this path, or the 'ensures' clause is too strong. The counterexample gives concrete inputs.
```

In a counterexample, `(Account 4 38)` is an account with `id = 4` and `balance = 38`.

- **Negative amount:** with `amount = -1` the transfer runs backwards and pulls money out of the destination. The balance check passes because `-1 > 0` is false, and the destination ends up with a balance of -1.
- **Same account:** both accounts in the second counterexample have `id = 4`. Nothing stops a transfer from an account to itself, which breaks the "two different accounts" guarantee. In a real system, two copies of one account would be written back and one update lost.

Nobody wrote a test for either case. The solver found them by searching for inputs that break the stated guarantee.

## Step 3: Fix the function, and the obligation moves to the caller

There are two changes:

- `amount: Int` becomes `amount: Money`, so a negative amount can't be passed in at all.
- The function returns `Err(SameAccount)` when the ids match.

```
fn transfer(src: Account, dst: Account, amount: Money) -> Result[Accounts, TransferError]
  ensures match result { Ok(moved) => src.id != dst.id && moved.source.balance + moved.target.balance == src.balance + dst.balance, Err(e) => true }
{
  if src.id == dst.id { return Err(SameAccount) }
  if amount > src.balance { return Err(InsufficientFunds(short: amount - src.balance)) }
  ...
}
```

Now `transfer` verifies. But a caller that computes the amount fails at its call site:

```
fn pay_invoice(customer: Account, shop: Account, invoice: Int, credit: Int) -> Result[Accounts, TransferError] {
  return transfer(src: customer, dst: shop, amount: invoice - credit)
}
```

```
examples/bank.vs(29,53): error TN3014: argument 'amount' of 'transfer' might not satisfy refinement type Money: self >= 0
  counterexample: customer = (Account 0 0), shop = (Account 0 0), invoice = -1, credit = 0
  hint: Every value of type Money must satisfy its 'where' clause.
```

Because `transfer` now demands a non-negative amount, every caller has to prove it passes one. Here `invoice - credit` goes negative when the invoice is negative or the credit exceeds it. The fix is a precondition that `pay_invoice` declares and its callers must meet:

```
fn pay_invoice(customer: Account, shop: Account, invoice: Int, credit: Int) -> Result[Accounts, TransferError]
  requires 0 <= credit && credit <= invoice
{
  return transfer(src: customer, dst: shop, amount: invoice - credit)
}
```

The requirement keeps moving up the call chain. When `main` makes a call that breaks it, such as `pay_invoice(customer: alice, shop: shop, invoice: 30, credit: 50)`, the compiler rejects that call:

```
bank_bad.vs(30,9): error TN3002: precondition of 'pay_invoice' might not hold: 0 <= credit && credit <= invoice
  counterexample: alice = (Account 1 100), shop = (Account 2 0)
  hint: The caller must establish every 'requires' clause of 'pay_invoice' before the call.
```

## Step 4: Make sure the contract says enough

The guarantee is only as strong as the contract. `Err(e) => true` lets `transfer` reject every request and still verify. A lazy or wrong implementation like this one passes:

```
  if src.id == dst.id || amount > 50 { return Err(SameAccount) }
```

To rule this out, add a second guarantee: when the accounts differ and the funds are there, the transfer succeeds.

```
  ensures src.id != dst.id && amount <= src.balance ==> match result { Ok(m) => true, Err(e) => false }
```

With that clause, the lazy version is rejected with the exact input it wrongly refuses:

```
error TN3001: postcondition of 'transfer' might not hold: src.id != dst.id && amount <= src.balance ==> (match result { Ok(m) => true, Err(e) => false })
  counterexample: src = (Account 4 51), dst = (Account 5 7719), amount = 51, result = (Err SameAccount)
```

The correct implementation still verifies.

## Step 5: It compiles only when everything is proved

```
> vsharpc run examples/bank.vs
ok: verified (15 proof obligations discharged) -> out\Bank.dll
Ok(value: Accounts(source: Account(id: 1, balance: 75), target: Account(id: 2, balance: 25)))
Err(error: InsufficientFunds(short: 400))
Err(error: SameAccount)
```

Those 15 obligations cover every possible input, not just the three calls in `main`:

- Both `ensures` clauses of `transfer` hold on every path.
- Every balance written into an `Account` is non-negative.
- Every call satisfies the callee's preconditions and refined parameter types.
- Everything terminates.

One thing is not proved by default: 64-bit overflow. Outside total mode, integer arithmetic traps with `OverflowException` at run time instead of wrapping around. Declaring `module Bank total` asks the verifier to prove that overflow can't happen, and it finds one more case:

```
examples/bank.vs(18,46): error TN3011: integer overflow possible: dst.balance + amount
  counterexample: src = (Account -1 1), dst = (Account 0 9223372036854775807), amount = 1, new_src = (Account -1 0)
  hint: In a 'total' function every Int operation must stay within 64 bits. Bound the operands with preconditions or invariants.
```

A destination already holding the maximum balance can't receive anything. Giving `Money` an upper bound doesn't make the problem go away; it turns it into a business decision the code has to make. With `type Money = Int where self >= 0 && self <= 1000000000000000`, the verifier reports that the destination's new balance might exceed the cap. It also reports that `pay_invoice` might pass an amount above the cap. `transfer` then needs a rule for full accounts, such as a new error case, and the success guarantee from Step 4 must allow for it.

`Bank.dll` is an ordinary .NET assembly that carries its contracts as attributes. Calls into it from C# skip the compile-time proof, so its public methods check `requires` clauses and refined parameters at run time. A C# call like `Bank.pay_invoice(alice, shop, 30, 50)` throws `VSharp.Runtime.ContractViolationException` instead of moving money. Calls between V# functions skip the check, because they were proved at compile time.

## What this means when writing an application

- **Your effort goes into the contract.** The two `ensures` lines and the `Money` type are the specification of this module. Getting them right is the job of a person or a planning model, and they're much shorter than the code.
- **The verifier is the reviewer.** It doesn't run your program on sample data; it searches for any input that breaks a guarantee. With `--json` each error is structured data with a code, a location and a counterexample, so an AI model can fix the code from it in a loop without anyone writing tests.
- **Edits stay local.** Each function is checked only against the contracts of the functions it calls. Changing `transfer`'s body re-proves only `transfer`. Changing its contract flags exactly the call sites that are now wrong, as Step 3 showed.
- **Check the contract, not just the code.** Step 4 is the part that verification can't do for you: a contract that promises too little is easy to satisfy. When reviewing V# code, ask what a wrong implementation could do and still verify.

## Try it

From the project directory:

```
dotnet run --project src/VSharp.Compiler -- check examples/bank.vs
dotnet run --project src/VSharp.Compiler -- run examples/bank.vs
dotnet run --project src/VSharp.Compiler -- check examples/bank.vs --json
```

To reproduce the errors, undo one fix at a time. For example, change `amount: Money` back to `amount: Int`, or delete the `requires` on `pay_invoice`.
