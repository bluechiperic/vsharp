// expect: TN2026
module Attributes

@NoSuchThing
type A = { x: Int }

@Obsolete(42)
type B = { x: Int }

@Serializable
fn f(x: Int) -> Int {
  return x
}

@Obsolete
spec fn g(x: Int) -> Int {
  x
}

type C = { @Obsolete("old", Bogus: true) x: Int }
