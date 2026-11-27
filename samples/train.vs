// A two-layer network trained on XOR. 'grad' derives the backward pass at compile time, the derived functions
// are type-checked and verified like hand-written ones, and the training step runs on the GPU when one is available.
module Train

type Params = { w1: Tensor[2, 8], b1: Tensor[8], w2: Tensor[8, 1], b2: Tensor[1] }

fn forward[B](x: Tensor[B, 2], w1: Tensor[2, 8], b1: Tensor[8], w2: Tensor[8, 1], b2: Tensor[1]) -> Tensor[B, 1] {
  let h = tanh(add_bias(matmul(x, w1), b1))
  return sigmoid(add_bias(matmul(h, w2), b2))
}

// Squared error, summed over the batch.
fn loss[B](x: Tensor[B, 2], y: Tensor[B, 1], w1: Tensor[2, 8], b1: Tensor[8], w2: Tensor[8, 1], b2: Tensor[1]) -> Float {
  let d = sub(forward(x, w1, b1, w2, b2), y)
  return sum(mul(d, d))
}

fn dw1 = grad loss wrt w1
fn db1 = grad loss wrt b1
fn dw2 = grad loss wrt w2
fn db2 = grad loss wrt b2

// The value-range contract is proved in the real-number model of tensors: sigmoid outputs lie in [0, 1].
fn predict[B](x: Tensor[B, 2], p: Params) -> Tensor[B, 1] effects device
  ensures forall e in elems(result) : 0.0 <= e && e <= 1.0
{
  return sigmoid(add_bias(matmul(tanh(add_bias(matmul(x, p.w1), p.b1)), p.w2), p.b2))
}

fn step[B](x: Tensor[B, 2], y: Tensor[B, 1], p: Params, lr: Float) -> Params effects device {
  let g1 = dw1(x, y, p.w1, p.b1, p.w2, p.b2)
  let g2 = db1(x, y, p.w1, p.b1, p.w2, p.b2)
  let g3 = dw2(x, y, p.w1, p.b1, p.w2, p.b2)
  let g4 = db2(x, y, p.w1, p.b1, p.w2, p.b2)
  return Params(w1: sub(p.w1, scale(g1, lr)),
                b1: sub(p.b1, scale(g2, lr)),
                w2: sub(p.w2, scale(g3, lr)),
                b2: sub(p.b2, scale(g4, lr)))
}

// Softmax rows are probability distributions: every entry is in [0, 1] and each row sums to 1.
fn classify[B](logits: Tensor[B, 3]) -> Tensor[B, 3]
  ensures forall e in elems(result) : 0.0 <= e && e <= 1.0
  ensures forall i in 0..B : row_sum(result, i) == 1.0
{
  return softmax(logits)
}

fn main() -> Unit effects device, io {
  let x = tensor[4, 2](0, 0,
                       0, 1,
                       1, 0,
                       1, 1)
  let y = tensor[4, 1](0, 1, 1, 0)
  var p = Params(w1: tensor[2, 8](0.5, -0.4, 0.3, -0.2, 0.6, -0.7, 0.1, 0.8,
                                  -0.6, 0.5, -0.3, 0.7, -0.1, 0.4, -0.8, 0.2),
                 b1: full[8](0.0),
                 w2: tensor[8, 1](0.3, -0.5, 0.2, -0.4, 0.6, -0.3, 0.5, -0.2),
                 b2: full[1](0.0))
  var epoch = 0
  while epoch < 3000
    invariant 0 <= epoch && epoch <= 3000
    decreases 3000 - epoch
  {
    if epoch % 1000 == 0 { print loss(x, y, p.w1, p.b1, p.w2, p.b2) }
    set p = step(x, y, p, 0.5)
    set epoch = epoch + 1
  }
  print loss(x, y, p.w1, p.b1, p.w2, p.b2)
  print predict(x, p)
  print classify(tensor[2, 3](1, 2, 3,
                              0, 0, 0))
}
