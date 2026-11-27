// expect: TN3003 TN3017
module ExceptionConditions

exception Frozen

exception Short(need: Int)

fn take(balance: Int, amount: Int, frozen: Bool) -> Int
  requires amount > 0
  ensures result == balance - amount
  throws Frozen when frozen
  throws Short when !frozen && amount > balance
{
  if frozen { throw Frozen }
  if amount > balance { throw Short(need: amount - balance) }
  return balance - amount
}

// The caller rules out Frozen but not Short.
fn careless(balance: Int, amount: Int) -> Int
  requires amount > 0
{
  return take(balance: balance, amount: amount, frozen: false)
}

// The condition promised to callers is narrower than the code.
fn lies(x: Int) -> Int
  throws Frozen when x > 10
{
  if x > 5 { throw Frozen }
  return x
}

// Short is thrown before the second assignment.
fn order(balance: Int) -> Int {
  var x = 0
  try {
    set x = 1
    let r = take(balance: balance, amount: 1, frozen: false)
    set x = 2
    return r
  } catch Short(need) {
    assert x == 2
  }
  return x
}
