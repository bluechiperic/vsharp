// expect: TN3011
// In total mode, a + b must be proved to fit in 64 bits.
module Bad

fn plus(a: Int, b: Int) -> Int total {
  return a + b
}
