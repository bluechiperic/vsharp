// Tensor shapes are part of the type. A shape error is a compile error, never a run-time surprise.
module Mlp

// B (batch), I (inputs) and O (outputs) are dimension parameters, solved at each call site.
fn dense[B, I, O](x: Tensor[B, I], w: Tensor[I, O], b: Tensor[O]) -> Tensor[B, O] {
  return add_bias(matmul(x, w), b)
}

fn mlp[B](x: Tensor[B, 3], w1: Tensor[3, 4], b1: Tensor[4], w2: Tensor[4, 2], b2: Tensor[2]) -> Tensor[B, 2] {
  let hidden = relu(dense(x, w1, b1))
  return dense(hidden, w2, b2)
}

fn main() -> Unit effects io {
  let x = tensor[2, 3](1, 2, 3,
                       -1, 0.5, 2)
  let w1 = tensor[3, 4](0.1, -0.2, 0.3, 0.4,
                        0.5, 0.6, -0.7, 0.8,
                        -0.9, 1.0, 0.2, -0.1)
  let b1 = tensor[4](0.1, 0.1, 0.1, 0.1)
  let w2 = tensor[4, 2](1, -1,
                        0.5, 0.5,
                        -1, 1,
                        0.25, 0)
  let b2 = tensor[2](0, 1)
  print mlp(x, w1, b1, w2, b2)
  print transpose(x)
}
