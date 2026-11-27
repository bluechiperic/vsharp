// expect: TN3008
// A contract that defines the result in terms of itself must not be accepted: it would make every proof vacuous.
module Bad

fn bad(x: Int) -> Int
  requires x >= 0
  ensures result == bad(x) + 1
  decreases x
{
  return 0
}
