// expect: TN3001
// Every comparison with NaN is false, so NaN falls through to 'return x'.
module Bad

fn clamp01(x: Float) -> Float
  ensures 0.0 <= result && result <= 1.0
{
  if x < 0.0 { return 0.0 }
  if x > 1.0 { return 1.0 }
  return x
}
