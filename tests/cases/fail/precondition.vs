// expect: TN3002
module Bad

fn pred(n: Int) -> Int
  requires n > 0
  ensures result == n - 1
{
  return n - 1
}

fn caller(n: Int) -> Int
  requires n >= 0
{
  return pred(n)
}
