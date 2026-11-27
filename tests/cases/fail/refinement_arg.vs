// expect: TN2020
module Bad

type Nat = Int where self >= 0

fn f(a: Array[Nat]) -> Int {
  return len(a)
}
