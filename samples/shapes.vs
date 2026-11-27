module Shapes

use System.ComponentModel
use System.Text.Json.Serialization

interface Shape {
  fn area(self) -> Decimal
    ensures result > 0m

  fn sides(self) -> Int
    ensures result >= 3
}

@Description("An axis-aligned rectangle")
class Rect(
  @JsonPropertyName("w") width: Decimal,
  @JsonPropertyName("h") height: Decimal
) implements Shape {
  invariant self.width > 0m
  invariant self.height > 0m

  fn area(self) -> Decimal {
    return self.width * self.height
  }

  fn sides(self) -> Int
    ensures result == 4
  {
    return 4
  }

  fn scaled(self, k: Decimal) -> Rect
    requires k > 0m
    ensures result.width == self.width * k
  {
    return self with { width: self.width * k, height: self.height * k }
  }
}

class Triangle(base: Decimal, height: Decimal) implements Shape {
  invariant self.base > 0m && self.height > 0m

  fn area(self) -> Decimal {
    return self.base * self.height / 2m
  }

  fn sides(self) -> Int {
    return 3
  }
}

fn total_area(shapes: Array[Shape]) -> Decimal
  ensures result >= 0m
{
  var total = 0m
  for i, s in shapes
    invariant total >= 0m
  {
    set total = total + s.area()
  }
  return total
}

fn larger(a: Shape, b: Shape) -> Shape {
  if a.area() >= b.area() { return a }
  return b
}

@Obsolete("Use total_area")
fn area_of_two(a: Shape, b: Shape) -> Decimal
  ensures result > 0m
{
  return a.area() + b.area()
}

fn main() -> Unit effects io {
  let r = Rect(width: 2m, height: 3m)
  let t = Triangle(base: 4m, height: 5m)
  let shapes: Array[Shape] = [r, t, r.scaled(2m)]
  print r
  print r.area()
  print r.sides()
  print t.area()
  print total_area(shapes)
  print larger(a: r, b: t)
  print larger(a: r, b: t).sides()
  print r == Rect(width: 2m, height: 3m)
}
