// Specification functions, lemmas, ghost code and termination measures. None of the proof machinery reaches the IL.
module Proofs

// A spec fn is a mathematical definition: usable in contracts and ghost code, never compiled.
spec fn sum_to(n: Int) -> Int
  requires n >= 0
  decreases n
{
  if n == 0 then 0 else n + sum_to(n - 1)
}

// A lemma is a proof by induction. Its body is ghost code; calling it makes its 'ensures' available.
lemma fn sum_formula(n: Int)
  requires n >= 0
  ensures 2 * sum_to(n) == n * (n + 1)
  decreases n
{
  if n > 0 { do sum_formula(n - 1) }
}

fn sum_loop(n: Int) -> Int
  requires n >= 0
  ensures result == sum_to(n)
{
  var acc = 0
  var i = 0
  while i < n
    invariant 0 <= i && i <= n
    invariant acc == sum_to(i)
    decreases n - i
  {
    set i = i + 1
    set acc = acc + i
  }
  return acc
}

// The closed form agrees with the definition, by the lemma. The lemma call is erased from the IL.
fn triangle(n: Int) -> Int
  requires 0 <= n && n <= 1000000
  ensures result == sum_to(n)
{
  do sum_formula(n)
  return n * (n + 1) / 2
}

// Ghost variables carry proof state; they are verified, then erased.
fn index_of_max(a: Array[Int]) -> Int
  requires len(a) > 0
  ensures 0 <= result && result < len(a)
  ensures forall k in 0..len(a) : a[k] <= a[result]
{
  var best = 0
  var i = 1
  ghost var steps = 0
  while i < len(a)
    invariant 1 <= i && i <= len(a)
    invariant 0 <= best && best < i
    invariant forall k in 0..i : a[k] <= a[best]
    invariant steps == i - 1
    decreases len(a) - i
  {
    if a[i] > a[best] { set best = i }
    set i = i + 1
    set steps = steps + 1
  }
  assert steps == len(a) - 1
  return best
}

// Mutual recursion: the two functions are proved terminating together.
fn is_even(n: Int) -> Bool
  requires n >= 0
  ensures result == (n % 2 == 0)
  decreases n
{
  if n == 0 { return true }
  return is_odd(n - 1)
}

fn is_odd(n: Int) -> Bool
  requires n >= 0
  ensures result == (n % 2 == 1)
  decreases n
{
  if n == 0 { return false }
  return is_even(n - 1)
}

// A lexicographic measure: each call decreases m, or keeps m and decreases n.
fn ack(m: Int, n: Int) -> Int
  requires m >= 0 && n >= 0
  ensures result > n
  decreases m, n
{
  if m == 0 { return n + 1 }
  if n == 0 { return ack(m: m - 1, n: 1) }
  return ack(m: m - 1, n: ack(m: m, n: n - 1))
}

// An unbounded quantifier. The trigger tells the solver to instantiate it only for pairs of reads a[i], a[j].
fn spread(a: Array[Int]) -> Int
  requires len(a) > 0
  requires forall i: Int, j: Int trigger a[i], a[j] : 0 <= i && i <= j && j < len(a) ==> a[i] <= a[j]
  ensures result >= 0
{
  return a[len(a) - 1] - a[0]
}

fn main() -> Unit effects io {
  print sum_loop(100)
  print triangle(100)
  print index_of_max([3, 9, 2, 7])
  print is_even(10)
  print is_odd(7)
  print ack(m: 2, n: 3)
  print spread([2, 3, 3, 8])
}
