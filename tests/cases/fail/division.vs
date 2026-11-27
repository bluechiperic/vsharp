// expect: TN3006
module Bad

fn average(total: Int, count: Int) -> Int
  requires count >= 0
{
  return total / count
}
