module Business

const WEEK: Int = 7

type Visit = { patient: String, day: Date, minutes: Int32, fee: Decimal }

fn label(v: Visit) -> String
  ensures str_starts_with(result, v.patient)
{
  return "{v.patient} on {v.day}: {v.minutes} min"
}

fn next_week(d: Date) -> Date
  requires days_between(date(2000, 1, 1), d) >= 0
  requires d <= date(9000, 1, 1)
  ensures days_between(d, result) == WEEK
{
  return add_days(d, WEEK)
}

fn leap_day() -> Date
  ensures month(result) == 2 && day(result) == 29 && year(result) == 2024
  ensures day_of_week(result) == 4
{
  return date(2024, 2, 29)
}

fn total_fee(vs: Array[Visit]) -> Decimal
  requires all(vs, v => v.fee >= 0m)
  ensures result >= 0m
{
  return sum_by(vs, v => v.fee)
}

fn long_visits(vs: Array[Visit]) -> Array[Visit]
  ensures all(result, v => v.minutes >= 60)
  ensures len(result) <= len(vs)
{
  return filter(vs, v => v.minutes >= 60)
}

fn kind(code: String) -> Int {
  match code {
    "A" | "B" { return 1 }
    "C" { return 2 }
    _ { return 0 }
  }
}

fn first_long(vs: Array[Visit]) -> Option[Visit]
  ensures match result { Some(v) => v.minutes >= 60, None => true }
{
  return find(vs, v => v.minutes >= 60)
}

fn count_to(n: Int) -> Int
  requires n >= 0
  ensures result == n
{
  var c = 0
  for i in 0..n
    invariant c == i
  {
    set c = c + 1
  }
  return c
}

fn first_negative(xs: Array[Int]) -> Int
  ensures result == -1 || 0 <= result && result < len(xs) && xs[result] < 0
{
  var found = -1
  for i, x in xs
    invariant found == -1 || 0 <= found && found < len(xs) && xs[found] < 0
  {
    if x < 0 {
      set found = i
      break
    }
  }
  return found
}

fn tally(words: Array[String]) -> Map[String, Int]
  ensures map_size(result) <= len(words)
{
  var m: Map[String, Int] = map_empty()
  for i, w in words
    invariant map_size(m) <= i
  {
    set m = map_put(m, w, map_get_or(m, w, 0) + 1)
  }
  return m
}

fn rename(v: Visit, who: String) -> Visit
  ensures result.patient == who && result.fee == v.fee
{
  return v with { patient: who }
}

fn rounded(x: Decimal) -> Decimal
  ensures x == 2.345m ==> result == 2.35m
  ensures x == -2.345m ==> result == -2.35m
{
  return dec_round(x, 2)
}

fn bits(mask: Int) -> Bool
  ensures mask == 5 ==> result
  ensures mask == 4 ==> !result
{
  return has_bit(mask, 0)
}

fn main() -> Unit effects io {
  let v = Visit(patient: "Ann", day: date(2024, 2, 29), minutes: 75, fee: 12.50m)
  let w = Visit(patient: "Bob", day: date(2024, 3, 1), minutes: 30, fee: 7m)
  let vs = [v, w]
  print label(v)
  print next_week(date(2024, 2, 26))
  print leap_day()
  print total_fee(vs)
  print long_visits(vs)
  print kind("B")
  print kind("C")
  print kind("Z")
  print first_long(vs)
  print first_long([w])
  print count_to(5)
  print first_negative([3, -1, -2])
  print tally(["a", "b", "a"])
  print rename(w, "Cy")
  print rounded(2.345m)
  print rounded(-2.345m)
  print bits(5)
  print sort_by_desc(vs, x => x.fee)
  print map(vs, x => x.minutes)
  print group_by(vs, x => x.minutes >= 60)
  print min_by(vs, x => x.patient)
  print fold(vs, 0, (acc, x) => acc + to_int(x.minutes))
  print parse_date("2024-12-01", "yyyy-MM-dd")
  print parse_int("x1")
  print unwrap_or(parse_int("42"), 0)
  print v == Visit(patient: "Ann", day: date(2024, 2, 29), minutes: 75, fee: 12.5m)
  print set_size(set_of(["a", "b", "a"]))
  print str_split("a,b,,c", ",")
  print to_str(day_of_week(date(2026, 11, 26)))
}
