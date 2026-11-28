module Hello

fn twice(n: Int) -> Int
  ensures result == n * 2
{
  return n + n
}
