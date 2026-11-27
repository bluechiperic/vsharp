// expect: TN2006 TN2013 TN2027 TN2029
module AsyncErrors

interface Store {
  fn load(self, key: Int) -> Int effects async
}

class Eager(n: Int) implements Store {
  fn load(self, key: Int) -> Int {
    return self.n
  }
}

fn get(s: Store) -> Int effects async {
  let v = await s.load(1)
  return v
}

fn plain(x: Int) -> Int {
  return x
}

fn forgets(s: Store) -> Int effects async {
  let v = get(s)
  return v
}

fn awaits_plain() -> Int effects async {
  let v = await plain(1)
  let w = await len([v])
  return w
}

fn not_async(s: Store) -> Int {
  let v = await get(s)
  return v
}

fn first[T](xs: Array[T]) -> Int effects async {
  return len(xs)
}
