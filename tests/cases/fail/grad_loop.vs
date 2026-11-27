// expect: TN2015
// Only straight-line code can be differentiated.
module Bad

fn f(x: Float) -> Float {
  var y = x
  var i = 0
  while i < 3
    invariant 0 <= i && i <= 3
    decreases 3 - i
  {
    set y = y * x
    set i = i + 1
  }
  return y
}

fn df = grad f wrt x
