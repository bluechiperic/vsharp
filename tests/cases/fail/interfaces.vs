// expect: TN2027 TN2028
module Interfaces

interface Counter {
  fn count(self) -> Int
    ensures result >= 0

  fn bump(self, by: Int) -> Int
}

class Missing(n: Int) implements Counter {
  fn count(self) -> Int
    requires self.n >= 0
  {
    return self.n
  }
}

class Wrong(n: Int) implements Counter {
  fn count(self) -> Int {
    return 0
  }

  fn bump(self, amount: Int) -> Int {
    return amount
  }
}

class Loud(n: Int) implements Counter {
  fn count(self) -> Int effects io {
    print self.n
    return 0
  }

  fn bump(self, by: Int) -> Int {
    return by
  }
}

class Wrap(inner: Counter) implements Counter {
  fn count(self) -> Int {
    return self.inner.count() + 1
  }

  fn bump(self, by: Int) -> Int {
    return by
  }
}
