// expect: TN3011
module Int32Total total

// In a total module Int32 arithmetic must provably fit in 32 bits.
fn double_it(x: Int32) -> Int32 {
  return x + x
}
