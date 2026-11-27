// expect: TN3014
module Bad

type Nat = Int where self >= 0

fn pred(n: Nat) -> Nat {
  return n - 1
}
