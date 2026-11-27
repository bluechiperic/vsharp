// expect: TN1001
module Bad

fn f(x: Int) -> Int {
  x = x + 1
  return x
}
