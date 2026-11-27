// Exceptions are part of a function's contract: 'throws E when cond' names an exception the function may throw and
// the only condition under which it does. Every exception is caught or declared, and the verifier proves the
// conditions, so a caller that rules them out needs no 'try' at all.
module Ledger

exception Overdrawn(balance: Decimal, amount: Decimal)

exception Frozen

exception BadAmount from "System.FormatException"

extern fn parse_amount(text: String) -> Decimal
  throws BadAmount
  from "System.Decimal.Parse"

extern fn pause(ms: Int32) -> Unit effects async from "System.Threading.Tasks.Task.Delay"

type Account = { owner: String, balance: Decimal, frozen: Bool }

type Moved = { source: Account, target: Account }

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

// The guard makes both 'when' conditions false, so nothing can escape and no 'try' is needed.
fn withdraw_if_possible(a: Account, amount: Decimal) -> Account
  requires amount > 0m
{
  if a.frozen || amount > a.balance { return a }
  return withdraw(a: a, amount: amount)
}

// A catch body knows the condition under which its exception was thrown.
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

// Exceptions that are not caught are declared, with conditions the verifier checks against the callee's.
fn transfer(src: Account, dst: Account, amount: Decimal) -> Moved
  requires amount > 0m
  ensures result.source.balance + result.target.balance == src.balance + dst.balance
  throws Frozen when src.frozen
  throws Overdrawn when amount > src.balance
{
  let a = withdraw(a: src, amount: amount)
  return Moved(source: a, target: dst with { balance: dst.balance + amount })
}

fn first_affordable(accounts: Array[Account], amount: Decimal) -> Int
  requires amount > 0m
  ensures result >= -1
{
  var found = -1
  for i, acct in accounts
    invariant found >= -1
  {
    try {
      do withdraw(a: acct, amount: amount)
      set found = i
      break
    } catch Frozen {
      continue
    } catch Overdrawn {
      continue
    }
  }
  return found
}

fn parse_or_zero(text: String) -> Decimal {
  try {
    let v = parse_amount(text)
    return v
  } catch BadAmount {
    return 0m
  }
}

exception UnknownCurrency(code: String)

// An implementation inherits the interface method's 'throws' clauses; .NET implementations may throw them too.
interface Rates {
  fn rate(self, currency: String) -> Decimal
    ensures result > 0m
    throws UnknownCurrency
}

class FixedRates(usd: Decimal) implements Rates {
  invariant self.usd > 0m

  fn rate(self, currency: String) -> Decimal {
    if currency == "USD" { return self.usd }
    throw UnknownCurrency(code: currency)
  }
}

fn convert(rates: Rates, amount: Decimal, currency: String) -> Decimal {
  try {
    let k = rates.rate(currency)
    return amount * k
  } catch UnknownCurrency {
    return 0m
  }
}

fn withdraw_later(a: Account, amount: Decimal) -> Account effects async
  requires amount > 0m
  throws Frozen when a.frozen
  throws Overdrawn when amount > a.balance
{
  do await pause(1)
  return withdraw(a: a, amount: amount)
}

fn main() -> Unit effects async, io {
  let alice = Account(owner: "alice", balance: 100m, frozen: false)
  let bob = Account(owner: "bob", balance: 5m, frozen: true)
  let carol = Account(owner: "carol", balance: 10m, frozen: false)
  print withdraw_if_possible(a: alice, amount: 30m).balance
  print try_withdraw(a: alice, amount: 500m)
  print try_withdraw(a: bob, amount: 1m)
  print try_withdraw(a: alice, amount: 40m)
  try {
    let moved = transfer(src: alice, dst: carol, amount: 200m)
    print moved
  } catch Overdrawn(balance, amount) {
    print "transfer refused: {amount} > {balance}"
  } catch Frozen {
    print "frozen"
  }
  print first_affordable(accounts: [bob, carol, alice], amount: 50m)
  print parse_or_zero("12.50")
  print parse_or_zero("twelve")
  let rates = FixedRates(usd: 2m)
  print convert(rates: rates, amount: 10m, currency: "USD")
  print convert(rates: rates, amount: 10m, currency: "EUR")
  try {
    let later = await withdraw_later(a: bob, amount: 1m)
    print later
  } catch Frozen {
    do await pause(1)
    print "bob is frozen"
  } catch Overdrawn {
    print "bob is short"
  }
}
