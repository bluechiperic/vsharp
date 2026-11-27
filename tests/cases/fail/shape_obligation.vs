// expect: TN3012
// 'H * W' and 'N' are different polynomials, so they are equal only if the precondition says so.
module Bad

fn flatten[B, N, H, W](x: Tensor[B, H, W], like: Tensor[B, N]) -> Tensor[B, N] {
  return reshape[B, N](x)
}
