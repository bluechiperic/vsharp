// expect: TN2001 TN2006 TN2027 TN2030
module ExceptionErrors

exception Frozen

exception Short(need: Int)

exception Anything from "System.Exception"

interface Store {
  fn get(self, k: Int) -> Int
    throws Frozen
}

class Bad(n: Int) implements Store {
  fn get(self, k: Int) -> Int
    throws Short
  {
    throw Short(need: k)
  }
}

fn risky(x: Int) -> Int
  throws Frozen
{
  if x > 0 { throw Frozen }
  return x
}

fn undeclared(x: Int) -> Int {
  return risky(x)
}

fn direct() -> Int {
  throw Short(need: 1)
}

fn useless(x: Int) -> Int {
  try {
    return x
  } catch Frozen {
    return 0
  }
}

spec fn s(x: Int) -> Int {
  risky(x)
}

fn unknown() -> Int
  throws Missing
{
  return 0
}
