// expect: TN3001
// A lemma is a theorem: its body must prove its 'ensures', just like a function.
module Bad

spec fn sq(x: Int) -> Int {
  x * x
}

lemma fn wrong(x: Int)
  ensures sq(x) > 0
{
}
