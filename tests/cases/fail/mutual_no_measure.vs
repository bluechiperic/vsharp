// expect: TN2011
module Bad

fn ping(n: Int) -> Int {
  if n <= 0 { return 0 }
  return pong(n - 1)
}

fn pong(n: Int) -> Int {
  if n <= 0 { return 1 }
  return ping(n - 1)
}
