// expect: TN3008
// The second call keeps m and does not decrease n, so the measure 'm, n' does not go down.
module Bad

fn ack(m: Int, n: Int) -> Int
  requires m >= 0 && n >= 0
  ensures result > n
  decreases m, n
{
  if m == 0 { return n + 1 }
  if n == 0 { return ack(m: m, n: 1) }
  return ack(m: m - 1, n: ack(m: m, n: n - 1))
}
