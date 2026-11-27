// expect: TN2008
module Bad

spec fn double(x: Int) -> Int {
  2 * x
}

fn f(x: Int) -> Int {
  return double(x)
}
