// expect: TN2003
module Bad

fn dense[B, I, O](x: Tensor[B, I], w: Tensor[I, O], b: Tensor[O]) -> Tensor[B, O] {
  return add_bias(matmul(x, w), b)
}

fn model[B](x: Tensor[B, 3], w: Tensor[4, 2], b: Tensor[2]) -> Tensor[B, 2] {
  return dense(x, w, b)
}
