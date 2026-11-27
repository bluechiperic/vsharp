// expect: TN3001
module Collections

fn sum_neg(xs: Array[Int]) -> Int
  ensures result >= 0
{
  return sum_by(xs, x => x)
}

fn count_up(n: Int) -> Int
  requires n >= 0
  ensures result == n + 1
{
  var c = 0
  for i in 0..n
    invariant c == i
  {
    set c = c + 1
  }
  return c
}

fn first_big(xs: Array[Int]) -> Option[Int]
  ensures match result { Some(x) => x > 10, None => true }
{
  return find(xs, x => x >= 10)
}
