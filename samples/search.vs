// Arrays are immutable values, so there is no aliasing to reason about.
module Search

// Proved: the result is a valid index holding the largest element.
fn index_of_max(a: Array[Int]) -> Int
  requires len(a) > 0
  ensures 0 <= result && result < len(a)
  ensures forall k in 0..len(a) : a[k] <= a[result]
{
  var best = 0
  var i = 1
  while i < len(a)
    invariant 1 <= i && i <= len(a)
    invariant 0 <= best && best < i
    invariant forall k in 0..i : a[k] <= a[best]
    decreases len(a) - i
  {
    if a[i] > a[best] { set best = i }
    set i = i + 1
  }
  return best
}

// Proved: returns an index of 'key', or -1 only when 'key' is absent. Every array access is proved in bounds.
fn binary_search(a: Array[Int], key: Int) -> Int
  requires forall i in 0..len(a) : forall j in i..len(a) : a[i] <= a[j]
  ensures -1 <= result && result < len(a)
  ensures result >= 0 ==> a[result] == key
  ensures result < 0 ==> forall k in 0..len(a) : a[k] != key
{
  var lo = 0
  var hi = len(a)
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= len(a)
    invariant forall k in 0..lo : a[k] < key
    invariant forall k in hi..len(a) : a[k] > key
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2
    if a[mid] < key { set lo = mid + 1 }
    else if a[mid] > key { set hi = mid }
    else { return mid }
  }
  return -1
}

// Proved: every element of the result is the square of its index.
fn squares(n: Int) -> Array[Int]
  requires n >= 0
  ensures len(result) == n
  ensures forall k in 0..n : result[k] == k * k
{
  var out = fill(n, 0)
  var i = 0
  while i < n
    invariant 0 <= i && i <= n
    invariant len(out) == n
    invariant forall k in 0..i : out[k] == k * k
    decreases n - i
  {
    set out = update(out, i, i * i)
    set i = i + 1
  }
  return out
}

fn main() -> Unit effects io {
  let xs = squares(8)
  print xs
  print binary_search(xs, 25)
  print binary_search(xs, 26)
  print index_of_max([3, 9, 2, 7])
}
