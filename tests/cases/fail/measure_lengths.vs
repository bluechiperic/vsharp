// expect: TN2012
module Bad

fn ping(n: Int, k: Int) -> Int
  requires n >= 0 && k >= 0
  decreases n, k
{
  if n == 0 { return k }
  return pong(n - 1)
}

fn pong(n: Int) -> Int
  requires n >= 0
  decreases n
{
  if n == 0 { return 0 }
  return ping(n: n - 1, k: 0)
}
