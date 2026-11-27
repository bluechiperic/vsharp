// expect: TN2016
module Bad

type Light = | Red | Amber | Green

fn next(l: Light) -> Light {
  return match l { Red => Green, Green => Amber }
}
