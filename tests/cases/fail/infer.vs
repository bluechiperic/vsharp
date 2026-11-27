// expect: TN2021
module Bad

fn main() -> Unit effects io {
  let xs = []
  print len(xs)
}
