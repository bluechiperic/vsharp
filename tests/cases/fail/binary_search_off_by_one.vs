// expect: TN3005
module Bad

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
    else if a[mid] > key { set hi = mid - 1 }
    else { return mid }
  }
  return -1
}
