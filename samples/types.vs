// Records, tagged unions, generics and refinement types. Every 'match' is checked for exhaustiveness.
module Types

type Nat = Int where self >= 0

type Point = { x: Int, y: Int }

type Shape = | Circle(r: Nat) | Rect(w: Nat, h: Nat) | Empty

type Pair[A, B] = { first: A, second: B }

// The result type is a refinement, so the verifier proves every return is non-negative.
fn area_x4(s: Shape) -> Nat {
  match s {
    Circle(r) { return 12 * r * r }
    Rect(w, h) { return 4 * w * h }
    Empty { return 0 }
  }
}

fn manhattan(p: Point) -> Nat {
  let dx = if p.x < 0 then -p.x else p.x
  let dy = if p.y < 0 then -p.y else p.y
  return dx + dy
}

// Result makes the failure case part of the type; the contract says exactly when each case happens.
fn safe_div(n: Int, d: Int) -> Result[Int, Int]
  ensures match result { Ok(q) => d != 0 && q == n / d, Err(e) => d == 0 && e == n }
{
  if d == 0 { return Err(n) }
  return Ok(n / d)
}

fn first[T](xs: Array[T]) -> Option[T]
  ensures match result { None => len(xs) == 0, Some(v) => len(xs) > 0 && v == xs[0] }
{
  if len(xs) == 0 { return None }
  return Some(xs[0])
}

fn swap[A, B](p: Pair[A, B]) -> Pair[B, A]
  ensures result.first == p.second && result.second == p.first
{
  return Pair(first: p.second, second: p.first)
}

fn or_else(o: Option[Int], fallback: Int) -> Int
  ensures match o { Some(v) => result == v, None => result == fallback }
{
  return match o { Some(v) => v, None => fallback }
}

// A Nat parameter is a precondition: V# callers must prove it, and the public .NET entry point checks it.
fn countdown(n: Nat) -> Array[Int]
  ensures len(result) == n
{
  var out = fill(n, 0)
  var i = 0
  while i < n
    invariant 0 <= i && i <= n
    invariant len(out) == n
    decreases n - i
  {
    set out = update(out, i, n - i)
    set i = i + 1
  }
  return out
}

fn main() -> Unit effects io {
  print area_x4(Circle(2))
  print area_x4(Rect(w: 3, h: 5))
  print area_x4(Empty)
  print manhattan(Point(x: -3, y: 4))
  print safe_div(n: 7, d: 2)
  print safe_div(n: 7, d: 0)
  print first([10, 20, 30])
  print or_else(o: first([]), fallback: -1)
  print swap(Pair(first: 1, second: true))
  print countdown(5)
}
