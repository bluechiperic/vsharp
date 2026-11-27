// Async functions compile to methods that return .NET Tasks. 'await' suspends without blocking a thread,
// and the verifier reasons about an awaited call the way it reasons about any call: through its contract.
module Tasks

extern fn pause(ms: Int32) -> Unit effects async from "System.Threading.Tasks.Task.Delay"

type Reading = | Value(n: Int) | Missing

interface Source {
  fn fetch(self, key: Int) -> Int effects async
    requires key >= 0
    ensures result >= key
}

class Doubler(offset: Int) implements Source {
  invariant self.offset >= 0

  fn fetch(self, key: Int) -> Int effects async {
    if key % 2 == 0 { do await pause(1) }
    return key * 2 + self.offset
  }
}

fn read(src: Source, key: Int) -> Reading effects async
  requires key >= 0
  ensures match result { Value(n) => n >= key, Missing => key == 0 }
{
  if key == 0 { return Missing }
  let n = await src.fetch(key)
  return Value(n)
}

fn sum_all(src: Source, n: Int) -> Int effects async
  requires n >= 0
  ensures result >= 0
{
  var total = 0
  for i in 0..n
    invariant total >= 0
  {
    let r = await read(src: src, key: i)
    match r {
      Value(v) { set total = total + v }
      Missing { do await pause(1) }
    }
  }
  return total
}

fn countdown(src: Source, from: Int) -> Int effects async
  requires from >= 0
  ensures result >= 0
{
  var k = from
  var last = 0
  while k > 0
    invariant k >= 0 && last >= 0
    decreases k
  {
    set last = await src.fetch(k)
    set k = k - 1
  }
  return last
}

fn twice(src: Source, key: Int) -> Int effects async
  requires key >= 0
  ensures result >= key
{
  return await src.fetch(key)
}

fn main() -> Unit effects async, io {
  let d = Doubler(offset: 1)
  let a = await read(src: d, key: 0)
  print a
  let b = await read(src: d, key: 3)
  print b
  let s = await sum_all(src: d, n: 4)
  print s
  let c = await countdown(src: d, from: 3)
  print c
  let t = await twice(src: d, key: 2)
  print t
  do await pause(1)
  print "done"
}
