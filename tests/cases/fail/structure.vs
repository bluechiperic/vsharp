// expect: TN2004 TN2005 TN2008 TN2010 TN2011
module Bad

fn f(x: Int) -> Int {
  let y = x
  set y = 1
  let x = 2
  let all = forall k in 0..x : k >= 0
  while y > 0 { set y = y - 1 }
}
