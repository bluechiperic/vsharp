// expect: TN3005
module Bad

fn count_up(n: Int) -> Int
  requires n >= 0
  ensures result == n
{
  var i = 0
  while i < n
    invariant i <= n
    decreases n - i
  {
    set i = i + 2
  }
  return i
}
