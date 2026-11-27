// Float is IEEE 754 binary64, and the verifier models it exactly: rounding, infinities and NaN included.
module Floats

// An extern binds a .NET method. Its contract is trusted, so state only what the method guarantees.
extern fn sqrt(x: Float) -> Float
  requires x >= 0.0
  ensures result >= 0.0
  from "System.Math.Sqrt"

// Without the NaN test this fails to verify: every comparison with NaN is false, so NaN would fall through.
fn clamp01(x: Float) -> Float
  ensures 0.0 <= result && result <= 1.0
{
  if x != x { return 0.0 }
  if x < 0.0 { return 0.0 }
  if x > 1.0 { return 1.0 }
  return x
}

fn distance(x: Float, y: Float) -> Float
  requires x == x && y == y
  ensures result >= 0.0
{
  return sqrt(x * x + y * y)
}

fn mean(a: Array[Float]) -> Float
  requires len(a) > 0
{
  var s = 0.0
  var i = 0
  while i < len(a)
    invariant 0 <= i && i <= len(a)
    decreases len(a) - i
  {
    set s = s + a[i]
    set i = i + 1
  }
  return s / to_float(len(a))
}

// Range facts about products are expensive to prove in exact IEEE arithmetic; a cheap test makes them unnecessary.
fn percent(x: Float) -> Int
  ensures 0 <= result && result <= 100
{
  let p = clamp01(x) * 100.0
  if p != p || p < 0.0 || p > 100.0 { return 0 }
  return trunc(p)
}

fn main() -> Unit effects io {
  print clamp01(1.7)
  print clamp01(-0.5)
  print distance(x: 3.0, y: 4.0)
  print mean([1.0, 2.0, 4.5])
  print percent(0.256)
}
