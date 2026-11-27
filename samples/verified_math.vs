// Contracts are proved at compile time. Nothing here is checked at run time.
module VerifiedMath

fn abs(x: Int) -> Int
  ensures result >= 0
  ensures result == x || result == -x
{
  if x < 0 { return -x }
  return x
}

fn clamp(x: Int, lo: Int, hi: Int) -> Int
  requires lo <= hi
  ensures lo <= result && result <= hi
  ensures lo <= x && x <= hi ==> result == x
{
  return if x < lo then lo else if x > hi then hi else x
}

// The contract of the recursive version is the mathematical definition of Fibonacci.
fn fib(n: Int) -> Int
  requires n >= 0
  ensures n < 2 ==> result == n
  ensures n >= 2 ==> result == fib(n - 1) + fib(n - 2)
  decreases n
{
  if n < 2 { return n }
  return fib(n - 1) + fib(n - 2)
}

// The loop is proved equal to the definition above for every n.
fn fib_fast(n: Int) -> Int
  requires n >= 0
  ensures result == fib(n)
{
  var a = 0
  var b = 1
  var i = 0
  while i < n
    invariant 0 <= i && i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    decreases n - i
  {
    let next = a + b
    set a = b
    set b = next
    set i = i + 1
  }
  return a
}

fn gcd(a: Int, b: Int) -> Int
  requires a >= 0 && b >= 0
  ensures result >= 0
  decreases b
{
  if b == 0 { return a }
  return gcd(a: b, b: a % b)
}

fn main() -> Unit effects io {
  print abs(-42)
  print clamp(x: 150, lo: 0, hi: 100)
  print fib_fast(50)
  print gcd(a: 1071, b: 462)
}
