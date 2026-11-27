// Appointment status and the check-in, check-out and cancel rules, ported from ScheduleAPI's AppointmentStatusService.
module Scheduling

const TICKS_PER_DAY: Int = 864000000000
const TICKS_PER_MINUTE: Int = 600000000
const TIME_FORMATS: Array[String] = ["h:mm tt", "hh:mm tt", "H:mm", "HH:mm", "h:mmtt", "hh:mmtt"]

type AppointmentStatus =
  | Scheduled
  | Late
  | Arrived
  | Departed
  | NoShow
  | CanceledShortNotice
  | Canceled
  | Deleted

// A missing start time is "".
type Schedule = { id: Int32, inactive: Bool, date: Option[Date], start_time: String }

// 'at' is DateTime.Ticks; a missing cancel notification is "".
type ScheduleAction = { schedule: Int32, kind: String, at: Int, cancel_notification: String }

// Arrived and Departed count whenever they were recorded, as in COM.
fn has_action(s: Schedule, actions: Array[ScheduleAction], kind: String) -> Bool
  ensures result ==> !s.inactive
{
  if s.inactive { return false }
  return any(actions, a => a.schedule == s.id && str_eq_ignore_case(a.kind, kind))
}

// The start as DateTime ticks. Only the six formats are understood; the original also falls back to DateTime.TryParse.
fn start_ticks(s: Schedule) -> Option[Int] {
  if str_is_blank(s.start_time) { return None }
  match s.date {
    Some(d) {
      match parse_time(str_trim(s.start_time), TIME_FORMATS) {
        Some(m) {
          return Some(days_between(date(1, 1, 1), d) * TICKS_PER_DAY + m * TICKS_PER_MINUTE)
        }
        None { }
      }
    }
    None { }
  }
  return None
}

spec fn is_open(st: AppointmentStatus) -> Bool {
  match st { Scheduled => true, Late => true, Arrived => true, Departed => true, _ => false }
}

fn status(s: Schedule, all_actions: Array[ScheduleAction], now: Int) -> AppointmentStatus
  ensures !s.inactive ==> is_open(result)
{
  let actions = filter(all_actions, a => a.schedule == s.id)
  if !s.inactive {
    if has_action(s, actions, "Departed") { return Departed }
    if has_action(s, actions, "Arrived") { return Arrived }
    match start_ticks(s) {
      Some(t) {
        if t < now { return Late }
      }
      None { }
    }
    return Scheduled
  }
  let terminal = filter(actions,
                        a => str_eq_ignore_case(a.kind, "Canceled") || str_eq_ignore_case(a.kind, "NoShow"))
  match max_by(terminal, a => a.at) {
    Some(latest) {
      match latest.cancel_notification {
        "NoShow" { return NoShow }
        "ShortNotice" { return CanceledShortNotice }
        _ { return Canceled }
      }
    }
    None { return Deleted }
  }
}

fn on_or_before(d: Option[Date], today: Date) -> Bool {
  return match d { Some(x) => x <= today, None => false }
}

fn can_check_in(s: Schedule, actions: Array[ScheduleAction], today: Date) -> Bool
  ensures result ==> !s.inactive && on_or_before(s.date, today)
{
  if s.inactive || !on_or_before(s.date, today) { return false }
  return !has_action(s, actions, "Arrived")
}

fn can_check_out(s: Schedule, actions: Array[ScheduleAction], today: Date) -> Bool
  ensures result ==> has_action(s, actions, "Arrived") && !has_action(s, actions, "Departed")
{
  if s.inactive || !on_or_before(s.date, today) { return false }
  return has_action(s, actions, "Arrived") && !has_action(s, actions, "Departed")
}

fn can_cancel(s: Schedule, actions: Array[ScheduleAction]) -> Bool
  ensures result ==> !s.inactive
{
  if s.inactive { return false }
  return !has_action(s, actions, "Arrived")
}
