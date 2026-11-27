// expect: TN3001 TN3006 TN3013
module Decimals

// Rounding is half away from zero: 2.345 rounds to 2.35.
fn bad_round(x: Decimal) -> Decimal
  ensures x == 2.345m ==> result == 2.34m
{
  return dec_round(x, 2)
}

fn rate(total: Decimal, hours: Decimal) -> Decimal {
  return total / hours
}

fn small(x: Int) -> Int32 {
  return to_int32(x)
}
