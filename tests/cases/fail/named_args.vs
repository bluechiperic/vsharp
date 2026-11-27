// expect: TN2014
// Two Int parameters: positional arguments could be swapped silently, so they must be named.
module Bad

fn minus(a: Int, b: Int) -> Int {
  return a - b
}

fn main() -> Unit effects io {
  print minus(1, 2)
}
