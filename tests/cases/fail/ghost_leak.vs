// expect: TN2018
// Ghost state is erased before code generation, so code that runs cannot depend on it.
module Bad

fn f(n: Int) -> Int {
  ghost let twice = 2 * n
  return twice
}
