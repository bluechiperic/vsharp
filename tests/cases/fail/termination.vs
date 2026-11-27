// expect: TN3008
module Bad

fn spin(n: Int) -> Int
  requires n >= 0
{
  var i = n
  while i > 0
    invariant i >= 0
    decreases i
  {
    set i = i + 0
  }
  return i
}

fn down(n: Int) -> Int
  decreases n
{
  return down(n - 1)
}
