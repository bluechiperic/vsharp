// expect: TN3013
module Bad

fn f(x: Float) -> Int {
  return trunc(x)
}
