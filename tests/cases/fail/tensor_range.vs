// expect: TN3001
// relu is non-negative but unbounded above, so this value-range contract is false.
module Bad

fn f[B](x: Tensor[B, 4]) -> Tensor[B, 4]
  ensures forall e in elems(result) : 0.0 <= e && e <= 1.0
{
  return relu(x)
}
