// expect: TN3016 TN3001
module ClassInvariant

interface Sized {
  fn size(self) -> Int
    ensures result > 0
}

class Range(lo: Int, hi: Int) implements Sized {
  invariant self.lo <= self.hi

  fn size(self) -> Int {
    return self.hi - self.lo
  }

  fn shifted(self, by: Int) -> Range {
    return self with { hi: self.hi + by }
  }
}

fn make(a: Int, b: Int) -> Range {
  return Range(lo: a, hi: b)
}
