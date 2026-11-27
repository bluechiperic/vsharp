// expect: TN4001
// A typed hole: the compiler reports what is known there and what the missing expression must satisfy.
module Holes

fn max(a: Int, b: Int) -> Int
  ensures result >= a && result >= b
{
  if a > b { return a }
  return ?answer
}
