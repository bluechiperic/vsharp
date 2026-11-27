// expect: TN3001 TN3015
module Dates

// 2024-02-29 is a Thursday (4), not a Wednesday.
fn wrong_weekday() -> Date
  ensures day_of_week(result) == 3
{
  return date(2024, 2, 29)
}

// 2023 is not a leap year.
fn not_leap() -> Date {
  return date(2023, 2, 29)
}

// d could be 9999-12-31.
fn next_week(d: Date) -> Date {
  return add_days(d, 7)
}
