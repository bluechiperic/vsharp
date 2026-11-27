// Recurring appointments, ported from ScheduleAPI's ScheduleHelper and RecurrencePattern.
module Scheduling

const LAST_DAY: Date = date(9999, 12, 31)

// A recurrence string: "<id>_<yyMMdd start>_<start time>_<end time>_<duration>_<yyMMdd end>_<end after>_<days>_<every x weeks>".
type Recurrence = {
  frequency: String,
  start_date: Date,
  start_time: String,
  end_time: String,
  duration: Int32,
  end_date: Option[Date],
  end_after: Option[Int32],
  days_of_week: Int32,
  every_x_weeks: Int32
}

// The days in a DaysOfWeekEnum mask (Sunday = 1, Monday = 2, ... Saturday = 64), as System.DayOfWeek numbers (Sunday = 0).
fn days_of_week(mask: Int32) -> Array[Int]
  ensures all(result, d => 0 <= d && d < 7 && has_bit(to_int(mask), d))
{
  return filter([0, 1, 2, 3, 4, 5, 6], d => has_bit(to_int(mask), d))
}

// The dates from 'start' on whose weekday is in 'mask', in every x-th week counted from the Monday on or before 'start'
// (a Sunday start counts from the next day, as the original does), until 'end' or until 'occurrences' dates are found.
// The original loops until DateTime overflows when neither limit is given and divides by zero when every_x_weeks is 0;
// here both are preconditions.
fn dates_for_days_of_week(mask: Int32, start: Date, every_x_weeks: Int32, end: Option[Date], occurrences: Option[Int32]) -> Array[Date]
  requires every_x_weeks != 0
  requires is_some(end) || is_some(occurrences)
  ensures all(result, d => start <= d && has_bit(to_int(mask), day_of_week(d)))
  ensures match occurrences { Some(n) => len(result) == 0 || len(result) <= to_int(n), None => true }
{
  let last = unwrap_or(end, LAST_DAY)
  let monday = add_days(start, 1 - day_of_week(start))
  let counting = is_some(occurrences)
  var left = to_int(unwrap_or(occurrences, 0))
  var dates: Array[Date] = []
  for k in 0..days_between(start, last) + 1
    invariant all(dates, d => start <= d && has_bit(to_int(mask), day_of_week(d)))
    invariant counting ==> len(dates) + left == to_int(unwrap_or(occurrences, 0))
                           && (len(dates) == 0 || left >= 0)
  {
    if counting && left <= 0 { break }
    let day = add_days(start, k)
    if has_bit(to_int(mask), day_of_week(day))
       && days_between(monday, day) / 7 % to_int(every_x_weeks) == 0 {
      set dates = append(dates, day)
      set left = left - 1
    }
  }
  return dates
}

fn int32_of(s: String) -> Option[Int32] {
  match parse_int(s) {
    Some(n) {
      if -2147483648 <= n && n <= 2147483647 { return Some(to_int32(n)) }
    }
    None { }
  }
  return None
}

// RecurrencePattern.Parse. The original throws on a malformed string; this returns None.
fn parse_recurrence(text: String) -> Option[Recurrence] {
  let parts = str_split(text, "_")
  if len(parts) < 9 { return None }
  let start = parse_date(parts[1], "yyMMdd")
  let duration = int32_of(parts[4])
  let days = int32_of(parts[7])
  let every = int32_of(parts[8])
  if is_none(start) || is_none(duration) || is_none(days) || is_none(every) { return None }
  var end_date: Option[Date] = None
  if parts[5] != "" {
    let parsed = parse_date(parts[5], "yyMMdd")
    if is_none(parsed) { return None }
    set end_date = parsed
  }
  var end_after: Option[Int32] = None
  if parts[6] != "" {
    let count = int32_of(parts[6])
    if is_none(count) { return None }
    set end_after = count
  }
  return Some(Recurrence(frequency: "D",
                         start_date: unwrap_or(start, LAST_DAY),
                         start_time: parts[2],
                         end_time: parts[3],
                         duration: unwrap_or(duration, 0),
                         end_date: end_date,
                         end_after: end_after,
                         days_of_week: unwrap_or(days, 0),
                         every_x_weeks: unwrap_or(every, 0)))
}
