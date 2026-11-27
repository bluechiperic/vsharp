// In a total module every Int operation is proved free of overflow, so no operation can trap at run time.
module Checked total

fn mid(lo: Int, hi: Int) -> Int
  requires 0 <= lo && lo <= hi
  ensures lo <= result && result <= hi
{
  return lo + (hi - lo) / 2
}

fn total_of(a: Array[Int]) -> Int
  requires len(a) <= 1000000
  requires forall k in 0..len(a) : 0 <= a[k] && a[k] <= 1000
  ensures 0 <= result && result <= 1000 * len(a)
{
  var s = 0
  var i = 0
  while i < len(a)
    invariant 0 <= i && i <= len(a)
    invariant 0 <= s && s <= 1000 * i
    decreases len(a) - i
  {
    set s = s + a[i]
    set i = i + 1
  }
  return s
}

fn main() -> Unit effects io {
  print mid(lo: 3, hi: 10)
  print total_of([1, 2, 3, 1000])
}
