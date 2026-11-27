// expect: TN2006
module Bad

fn noisy(x: Int) -> Int {
  print x
  return x
}
