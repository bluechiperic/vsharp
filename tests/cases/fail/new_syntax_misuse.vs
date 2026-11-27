// expect: TN2002 TN2016 TN2023 TN2024 TN2025
module Misuse

const LIMIT: Int = BASE + 1
const BASE: Int = 10

type Reading = { at: Date, value: Float }

fn loose() -> Int {
  break
  return 0
}

fn twice(n: Int) -> Int {
  return n * 2
}

fn keep() -> Int {
  return twice(x => x + 1)
}

fn by_value(rs: Array[Reading]) -> Map[Float, Int] {
  return to_map(rs, r => r.value, r => 1)
}

fn grade(code: String) -> Int {
  match code {
    "A" { return 4 }
    "B" { return 3 }
  }
  return 0
}
