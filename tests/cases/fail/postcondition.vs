// expect: TN3001
module Bad

fn abs(x: Int) -> Int
  ensures result >= 0
{
  if x < 0 { return x }
  return x
}
