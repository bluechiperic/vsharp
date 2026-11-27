// expect: TN3009
module Bad

fn impossible(x: Int) -> Int
  requires x > 0 && x < 0
  ensures result == 42
{
  return 0
}
