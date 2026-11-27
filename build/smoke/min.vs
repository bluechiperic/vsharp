module Smoke

fn inc(n: Int) -> Int
  requires n >= 0
  ensures result == n + 1
{
  return n + 1
}
