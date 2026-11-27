// expect: TN2019
module Bad

fn f(a: Array[Int]) -> Int
  requires forall i: Int : 0 <= i && i < len(a) ==> a[i] >= 0
{
  return 0
}
