// Authorization limits (visits, units, days, dollars) per payer, ported from ScheduleAPI's AuthorizationCheckService.
// The C# shell loads the projection data set and passes its tables in; everything after that is here.
module Scheduling

const DISCIPLINES: Array[String] = ["PT", "OT", "ST"]

const UNDER_LIMIT: String = "UnderLimit"
const AT_LIMIT: String = "AtLimit"
const OVER_LIMIT: String = "OverLimit"
const REQUIRED_NOT_SET: String = "AuthorizationRequiredButNotSet"
const NOT_REQUIRED: String = "PlanDoesNotRequireAuthorization"
const NOT_CONFIGURED: String = "CoverageNotConfigured"

const THIS_AUTH: String = "THISAUTH"
const CALENDAR_YEAR: String = "CY"

// Missing strings are "". Dates are calendar days (the tables hold midnight values).
type PatientCase = { id: Int32, pps_track: Option[Int32], start: Date, end: Option[Date] }

type CasePayerSet = {
  patient_case: Int32,
  from: Date,
  thru: Option[Date],
  discipline: String,
  payer_set: Option[Int32],
  pps_track: Option[Int32]
}

type PayerSequence = { payer_set: Int32, resident_payer: Option[Int32], sequence: Int32 }
type ResidentPayer = { id: Int32, payer_type: Int32 }
type PayerType = { id: Int32, requires_authorization: Bool }
type Authorization = { id: Int32, resident_payer: Int32, from: Date, thru: Option[Date] }

type AuthLimit = {
  authorization: Int32,
  kind: String,
  discipline: String,
  limit: Decimal,
  frequency: String,
  prior_usage: Decimal
}

type TxTrack = { id: Int32, patient_case: Int32, discipline: String }

type TxSession = {
  id: Int32,
  track: Int32,
  date: Date,
  visit_number: Int32,
  deleted: Bool,
  missed_reason: String
}

type TxMinute = { session: Int32, units: Int32 }

type ScheduledItem = {
  id: Int32,
  discipline: String,
  date: Option[Date],
  inactive: Bool,
  individual: Int32,
  group: Int32,
  concurrent: Int32,
  eval: Int32
}

type Tables = {
  patient_cases: Array[PatientCase],
  case_payer_sets: Array[CasePayerSet],
  sequences: Array[PayerSequence],
  resident_payers: Array[ResidentPayer],
  payer_types: Array[PayerType],
  authorizations: Array[Authorization],
  limits: Array[AuthLimit],
  tracks: Array[TxTrack],
  sessions: Array[TxSession],
  minutes: Array[TxMinute],
  schedules: Array[ScheduledItem]
}

type Visit = { date: Date, discipline: String, units: Int32 }

type Limitation = {
  disciplines: Array[String],
  resident_payer: Int32,
  from: Date,
  thru: Option[Date],
  limit: Decimal,
  remaining: Decimal,
  kind: String,
  frequency: String
}

type Coverage = { resident_payer: Int32, requires_authorization: Bool }

// The limitations after applying a visit, and the visit's status.
type Step = { limits: Array[Limitation], status: String }

type Processed = {
  limits: Array[Limitation],
  statuses: Array[String],
  payers: Array[Option[Int32]]
}

type LimitationView = {
  resident_payer: Int32,
  kind: String,
  frequency: String,
  disciplines: Array[String],
  limit: Decimal,
  remaining: Decimal,
  used: Decimal,
  status: String,
  from: Date,
  thru: Option[Date],
  description: String
}

type SummaryLine = {
  discipline: String,
  status: String,
  text: String,
  remaining: Decimal,
  visible: Bool,
  warning: Bool
}

type AuthorizationCheck = {
  patient_case: Int32,
  current_status: Map[String, String],
  current: Array[LimitationView],
  all: Array[LimitationView],
  summary: Array[SummaryLine]
}

// ---------- dates ----------
fn before_end(d: Date, end: Option[Date]) -> Bool {
  return match end { Some(e) => d <= e, None => true }
}

fn within(d: Date, from: Date, thru: Option[Date]) -> Bool {
  return from <= d && before_end(d, thru)
}

fn is_value(o: Option[Int32], v: Int32) -> Bool {
  return match o { Some(x) => x == v, None => false }
}

fn later(a: Date, b: Date) -> Date
  ensures result >= a && result >= b && (result == a || result == b)
{
  return if a > b then a else b
}

fn earlier(a: Date, b: Date) -> Date
  ensures result <= a && result <= b && (result == a || result == b)
{
  return if a < b then a else b
}

// ---------- patient case and coverage ----------
fn find_patient_case(t: Tables, pps_track: Option[Int32], patient_case: Option[Int32]) -> Option[PatientCase] {
  match patient_case {
    Some(id) { return find(t.patient_cases, pc => pc.id == id) }
    None { }
  }
  match pps_track {
    Some(track) {
      match find(t.case_payer_sets, c => is_value(c.pps_track, track)) {
        Some(cps) { return find(t.patient_cases, pc => pc.id == cps.patient_case) }
        None { }
      }
    }
    None { }
  }
  return max_by(t.patient_cases, pc => pc.start)
}

fn covers_discipline(c: CasePayerSet, discipline: String) -> Bool {
  return str_is_blank(c.discipline) || str_trim(c.discipline) == discipline
}

// The case payer set for a date and discipline: one naming the discipline wins over a blank one. Outside every date
// range (the status check uses the last scheduled date), the latest set for the discipline is used.
fn find_case_payer_set(t: Tables, d: Date, discipline: String) -> Option[CasePayerSet] {
  let dated = filter(t.case_payer_sets,
                     c => within(d: d, from: c.from, thru: c.thru) && covers_discipline(c, discipline))
  match find(dated, c => !str_is_blank(c.discipline)) {
    Some(named) { return Some(named) }
    None { }
  }
  match find(dated, c => str_is_blank(c.discipline)) {
    Some(blank) { return Some(blank) }
    None { }
  }
  var best: Option[CasePayerSet] = None
  for candidate in t.case_payer_sets {
    if covers_discipline(candidate, discipline) {
      match best {
        Some(b) {
          if candidate.from > b.from
             || candidate.from == b.from
                && str_is_blank(b.discipline)
                && !str_is_blank(candidate.discipline) {
            set best = Some(candidate)
          }
        }
        None { set best = Some(candidate) }
      }
    }
  }
  return best
}

fn find_coverage(t: Tables, d: Date, discipline: String) -> Option[Coverage] {
  match find_case_payer_set(t, d, discipline) {
    Some(cps) {
      match cps.payer_set {
        Some(set_id) {
          match find(t.sequences, s => s.payer_set == set_id && s.sequence == 1) {
            Some(primary) {
              match primary.resident_payer {
                Some(rp_id) {
                  match find(t.resident_payers, rp => rp.id == rp_id) {
                    Some(rp) {
                      let payer_type = find(t.payer_types, pt => pt.id == rp.payer_type)
                      let needs_auth = match payer_type { Some(ty) => ty.requires_authorization, None => false }
                      return Some(Coverage(resident_payer: rp.id, requires_authorization: needs_auth))
                    }
                    None { }
                  }
                }
                None { }
              }
            }
            None { }
          }
        }
        None { }
      }
    }
    None { }
  }
  return None
}

// ---------- limitations ----------
fn filter_authorizations(auths: Array[Authorization], pc: PatientCase) -> Array[Authorization] {
  let overlapping = filter(auths,
                           a => before_end(a.from, pc.end)
                                && before_end(pc.start, a.thru)
                                && before_end(a.from, a.thru))
  return sort_by(overlapping, a => a.from)
}

fn parse_disciplines(s: String) -> Array[String] {
  if str_is_blank(s) { return [] }
  return filter(map(str_split(s, ","), x => str_trim(x)), x => x != "")
}

fn stub(l: AuthLimit, a: Authorization, from: Date, thru: Option[Date]) -> Limitation {
  return Limitation(disciplines: parse_disciplines(l.discipline),
                    resident_payer: a.resident_payer,
                    from: from,
                    thru: thru,
                    limit: l.limit,
                    remaining: l.limit - l.prior_usage,
                    kind: str_upper(l.kind),
                    frequency: str_upper(l.frequency))
}

// This-authorization limits first, then calendar-year limits split into one per year the authorization spans.
fn build_limitations(auths: Array[Authorization], limits: Array[AuthLimit], max_thru: Date) -> Array[Limitation] {
  let relevant = filter(limits, l => any(auths, a => a.id == l.authorization))
  var out: Array[Limitation] = []
  for l in relevant {
    if str_eq_ignore_case(l.frequency, THIS_AUTH) {
      match find(auths, a => a.id == l.authorization) {
        Some(this_auth) {
          set out = append(out,
                           stub(l: l, a: this_auth, from: this_auth.from, thru: this_auth.thru))
        }
        None { }
      }
    }
  }
  for cy in relevant {
    if str_eq_ignore_case(cy.frequency, CALENDAR_YEAR) {
      match find(auths, a => a.id == cy.authorization) {
        Some(auth) {
          let last = unwrap_or(auth.thru, max_thru)
          for y in year(auth.from)..year(last) + 1 {
            let first_day = later(a: date(y, 1, 1), b: auth.from)
            let last_day = earlier(a: date(y, 12, 31), b: last)
            set out = append(out, stub(l: cy, a: auth, from: first_day, thru: Some(last_day)))
          }
        }
        None { }
      }
    }
  }
  return out
}

fn matches(l: Limitation, kind: String, frequency: String, discipline: String, d: Date, payer: Int32) -> Bool {
  return str_eq_ignore_case(l.kind, kind)
         && any(l.disciplines, x => x == discipline)
         && str_eq_ignore_case(l.frequency, frequency)
         && within(d: d, from: l.from, thru: l.thru)
         && l.resident_payer == payer
}

// The first matching limitation with a balance left, else the last matching one (so visits past the cap get a status).
fn find_limitation(limits: Array[Limitation], kind: String, frequency: String, discipline: String, d: Date, payer: Int32) -> Int
  ensures -1 <= result && result < len(limits)
{
  var last = -1
  for i, l in limits
    invariant -1 <= last && last < len(limits)
  {
    if matches(l: l,
               kind: kind,
               frequency: frequency,
               discipline: discipline,
               d: d,
               payer: payer) {
      if l.remaining > 0m { return i }
      set last = i
    }
  }
  return last
}

fn apply_status(current: String, remaining: Decimal) -> String {
  if remaining < 0m { return OVER_LIMIT }
  if remaining == 0m && current != OVER_LIMIT { return AT_LIMIT }
  if current != OVER_LIMIT && current != AT_LIMIT { return UNDER_LIMIT }
  return current
}

fn apply_limitation(s: Step, v: Visit, kind: String, frequency: String, payer: Int32, mock: Bool) -> Step
  ensures len(result.limits) == len(s.limits)
{
  let i = find_limitation(limits: s.limits,
                          kind: kind,
                          frequency: frequency,
                          discipline: v.discipline,
                          d: v.date,
                          payer: payer)
  if i < 0 { return s }
  let l = s.limits[i]
  let remaining = if mock then l.remaining else l.remaining - 1m
  let limits = if mock then s.limits else update(s.limits, i, l with { remaining: remaining })
  return Step(limits: limits, status: apply_status(s.status, remaining))
}

fn apply_kind(s: Step, v: Visit, kind: String, amount: Int, payer: Int32, mock: Bool) -> Step
  ensures len(result.limits) == len(s.limits)
{
  var step = s
  for k in 0..amount
    invariant len(step.limits) == len(s.limits)
  {
    set step = apply_limitation(s: step,
                                v: v,
                                kind: kind,
                                frequency: THIS_AUTH,
                                payer: payer,
                                mock: mock)
    set step = apply_limitation(s: step,
                                v: v,
                                kind: kind,
                                frequency: CALENDAR_YEAR,
                                payer: payer,
                                mock: mock)
  }
  return step
}

fn process_visits(t: Tables, visits: Array[Visit], days: Array[Visit], limits: Array[Limitation], mock: Bool) -> Processed
  ensures len(result.statuses) == len(visits) && len(result.payers) == len(visits)
  ensures len(result.limits) == len(limits)
{
  var current = limits
  var statuses: Array[String] = []
  var payers: Array[Option[Int32]] = []
  for i, v in visits
    invariant len(statuses) == i && len(payers) == i && len(current) == len(limits)
  {
    match find_coverage(t, v.date, v.discipline) {
      Some(c) {
        set payers = append(payers, Some(c.resident_payer))
        if !c.requires_authorization {
          set statuses = append(statuses, NOT_REQUIRED)
        } else {
          var step = Step(limits: current, status: REQUIRED_NOT_SET)
          set step = apply_kind(step, v, "VISITS", 1, c.resident_payer, mock)
          set step = apply_kind(step, v, "UNITS", to_int(v.units), c.resident_payer, mock)
          // A separate days list does the counting; visits then only take the days status.
          set step = apply_kind(step, v, "DAYS", 1, c.resident_payer, len(days) > 0 || mock)
          set step = apply_kind(step, v, "DOLLARS", 1, c.resident_payer, mock)
          set current = step.limits
          set statuses = append(statuses, step.status)
        }
      }
      None {
        set payers = append(payers, None)
        set statuses = append(statuses, NOT_CONFIGURED)
      }
    }
  }
  for day in days
    invariant len(current) == len(limits)
  {
    match find_coverage(t, day.date, day.discipline) {
      Some(day_coverage) {
        if day_coverage.requires_authorization {
          let counted = apply_kind(Step(limits: current, status: REQUIRED_NOT_SET),
                                   day,
                                   "DAYS",
                                   1,
                                   day_coverage.resident_payer,
                                   mock)
          set current = counted.limits
        }
      }
      None { }
    }
  }
  return Processed(limits: current, statuses: statuses, payers: payers)
}

// ---------- visits and schedules ----------
fn counted_session(s: TxSession, case_tracks: Array[TxTrack]) -> Bool {
  return any(case_tracks, tr => tr.id == s.track)
         && !s.deleted
         && str_is_blank(s.missed_reason)
}

fn same_group(a: TxSession, b: TxSession, by_visit: Bool) -> Bool {
  return a.date == b.date
         && a.track == b.track
         && (!by_visit || a.visit_number == b.visit_number)
}

// The first session (lowest id) of each date and track, and also visit number when 'by_visit', by date then id.
fn first_sessions(t: Tables, case_tracks: Array[TxTrack], by_visit: Bool) -> Array[TxSession] {
  let counted = filter(t.sessions, s => counted_session(s, case_tracks))
  let firsts = filter(counted,
                      s => !any(counted, o => same_group(a: o, b: s, by_visit: by_visit) && o.id < s.id))
  return sort_by(sort_by(firsts, s => s.id), s => s.date)
}

fn track_discipline(case_tracks: Array[TxTrack], track: Int32) -> String {
  return match find(case_tracks, tr => tr.id == track) { Some(tr) => tr.discipline, None => "" }
}

fn session_units(t: Tables, session: Int32) -> Int32 {
  return sum_by(filter(t.minutes, m => m.session == session && m.units > 0),
                m => m.units)
}

fn activity_minutes(s: ScheduledItem) -> Int {
  return to_int(s.individual) + to_int(s.group) + to_int(s.concurrent) + to_int(s.eval)
}

fn is_on(d: Option[Date], day: Date) -> Bool {
  return match d { Some(x) => x == day, None => false }
}

fn is_after(d: Option[Date], day: Date) -> Bool {
  return match d { Some(x) => x > day, None => false }
}

fn has_visit(visits: Array[Visit], day: Date, discipline: String) -> Bool {
  return any(visits, v => v.date == day && v.discipline == discipline)
}

// The last active future schedule date for a discipline, or today.
fn thru_date(schedules: Array[ScheduledItem], discipline: String, today: Date) -> Date
  ensures result >= today
{
  let future = filter(schedules,
                      s => s.discipline == discipline
                           && is_after(s.date, today)
                           && !s.inactive
                           && activity_minutes(s) > 0)
  let last = fold(future, today, (m, s) => later(a: m, b: unwrap_or(s.date, today)))
  return later(a: last, b: today)
}

// ---------- results ----------
fn pad4(n: Int) -> String {
  let s = to_str(n)
  if str_len(s) >= 4 { return s }
  return str_sub("0000", 0, 4 - str_len(s)) + s
}

// M/d/yyyy
fn date_text(d: Date) -> String {
  return "{month(d)}/{day(d)}/{pad4(year(d))}"
}

fn optional_date_text(d: Option[Date]) -> String {
  return match d { Some(x) => date_text(x), None => "" }
}

// The .NET custom format "###0" for a decimal: rounded half away from zero, and "0" (never "-0") for a small negative.
fn whole(x: Decimal) -> String {
  return to_str(dec_round(x, 0))
}

fn limit_status(remaining: Decimal) -> String {
  return if remaining > 0m then UNDER_LIMIT else if remaining < 0m then OVER_LIMIT else AT_LIMIT
}

fn describe(l: Limitation, used: Decimal) -> String {
  let range = "{date_text(l.from)} - {optional_date_text(l.thru)}"
  let who = str_join(l.disciplines, ",")
  let label = if str_eq_ignore_case(l.frequency, CALENDAR_YEAR) then "Calendar Year Visits" else "Visits"
  match str_upper(l.kind) {
    "VISITS" {
      return "{whole(used)} visits / {whole(l.limit)} authorized {label} by {who} from {range}"
    }
    "UNITS" { return "{who} Authorization of {whole(l.limit)} Units is set from {range}" }
    "DAYS" { return "{whole(used)} days / {whole(l.limit)} authorized days by {who} from {range}" }
    "DOLLARS" { return "{who} Authorization of ${whole(l.limit)} is set from {range}" }
    _ { return "{who} authorization from {range}" }
  }
}

fn view(l: Limitation) -> LimitationView {
  let used = l.limit - l.remaining
  return LimitationView(resident_payer: l.resident_payer,
                        kind: l.kind,
                        frequency: l.frequency,
                        disciplines: l.disciplines,
                        limit: l.limit,
                        remaining: l.remaining,
                        used: used,
                        status: limit_status(l.remaining),
                        from: l.from,
                        thru: l.thru,
                        description: describe(l, used))
}

fn status_text(value: String) -> String {
  match value {
    "UnderLimit" { return "Authorized" }
    "AtLimit" { return "Authorization limitation has been reached" }
    "OverLimit" { return "Authorization limitation has been exceeded" }
    "PlanDoesNotRequireAuthorization" { return "Payer does not require authorization" }
    "CoverageNotConfigured" { return "Payer coverage has not been configured" }
    "AuthorizationRequiredButNotSet" { return "Authorization is required, but has not been set" }
    _ { return "Unknown status" }
  }
}

fn unit_name(kind: String) -> String {
  match str_upper(kind) {
    "VISITS" { return "visit" }
    "UNITS" { return "unit" }
    "DAYS" { return "day" }
    "DOLLARS" { return "dollar" }
    _ { return "item" }
  }
}

fn remaining_text(remaining: Decimal, unit: String) -> String {
  let size = if remaining < 0m then -remaining else remaining
  let plural = if size == 1m then "" else "s"
  if remaining == 0m { return "Authorized limit reached, 0 {unit}s remaining" }
  if remaining < 0m {
    return "Authorization limit has been exceeded by {whole(size)} {unit}{plural}"
  }
  return "{whole(remaining)} {unit}{plural} remaining"
}

fn summary(current_status: Map[String, String], current: Array[LimitationView]) -> Array[SummaryLine] {
  var lines: Array[SummaryLine] = []
  for d in DISCIPLINES {
    let state = map_get_or(current_status, d, NOT_CONFIGURED)
    if state == NOT_CONFIGURED || state == NOT_REQUIRED || state == REQUIRED_NOT_SET {
      set lines = append(lines,
                         SummaryLine(discipline: d,
                                     status: state,
                                     text: "{d} {status_text(state)}",
                                     remaining: 0m,
                                     visible: state != NOT_REQUIRED,
                                     warning: state == REQUIRED_NOT_SET || state == NOT_CONFIGURED))
      continue
    }
    let mine = filter(current, l => any(l.disciplines, x => x == d))
    if len(mine) == 0 {
      set lines = append(lines,
                         SummaryLine(discipline: d,
                                     status: state,
                                     text: "{d} {status_text(state)}",
                                     remaining: 0m,
                                     visible: true,
                                     warning: state == OVER_LIMIT || state == AT_LIMIT))
      continue
    }
    for lim in mine {
      set lines = append(lines,
                         SummaryLine(discipline: d,
                                     status: lim.status,
                                     text: "{d} {remaining_text(lim.remaining, unit_name(lim.kind))}",
                                     remaining: lim.remaining,
                                     visible: true,
                                     warning: lim.status == OVER_LIMIT || lim.status == AT_LIMIT || lim.remaining <= 2m))
    }
  }
  return lines
}

fn status_map(statuses: Array[String]) -> Map[String, String]
  requires len(statuses) == len(DISCIPLINES)
{
  var m: Map[String, String] = map_empty()
  for i, d in DISCIPLINES {
    set m = map_put(m, d, statuses[i])
  }
  return m
}

// ---------- the check ----------
// CheckAuthorization after the data set is loaded: the explicit patient case, else the one for the PPS track, else the latest.
fn check(t: Tables, pps_track: Option[Int32], patient_case: Option[Int32], today: Date) -> AuthorizationCheck {
  match find_patient_case(t: t, pps_track: pps_track, patient_case: patient_case) {
    Some(pc) { return check_case(t, pc, today) }
    None {
      return AuthorizationCheck(patient_case: 0,
                                current_status: status_map([NOT_CONFIGURED, NOT_CONFIGURED, NOT_CONFIGURED]),
                                current: [],
                                all: [],
                                summary: [])
    }
  }
}

fn check_case(t: Tables, pc: PatientCase, today: Date) -> AuthorizationCheck {
  let thru = map(DISCIPLINES, d => thru_date(t.schedules, d, today))
  let max_thru = fold(thru, today, (m, d) => later(a: m, b: d))
  let limits = build_limitations(filter_authorizations(t.authorizations, pc),
                                 t.limits,
                                 max_thru)

  let case_tracks = filter(t.tracks, tr => tr.patient_case == pc.id)
  let visits = map(first_sessions(t, case_tracks, true),
                   s => Visit(date: s.date,
                              discipline: track_discipline(case_tracks, s.track),
                              units: session_units(t, s.id)))
  let days = map(first_sessions(t, case_tracks, false),
                 s => Visit(date: s.date,
                            discipline: track_discipline(case_tracks, s.track),
                            units: 0))
  let actual = process_visits(t: t, visits: visits, days: days, limits: limits, mock: false)

  // Today's schedules count only where no session exists for that discipline today.
  let today_items = filter(t.schedules,
                           s => is_on(s.date, today)
                                && !s.inactive
                                && activity_minutes(s) > 0
                                && !has_visit(visits, today, s.discipline))
  let scheduled_today = process_visits(t: t,
                                       visits: map(today_items, s => Visit(date: today, discipline: s.discipline, units: 0)),
                                       days: [],
                                       limits: actual.limits,
                                       mock: false)
  let future_items = sort_by(filter(t.schedules,
                                    s => is_after(s.date, today) && !s.inactive && activity_minutes(s) > 0),
                             s => unwrap_or(s.date, today))
  let future_visits = map(future_items,
                          s => Visit(date: unwrap_or(s.date, today), discipline: s.discipline, units: 0))
  let scheduled = process_visits(t: t,
                                 visits: future_visits,
                                 days: [],
                                 limits: scheduled_today.limits,
                                 mock: false)

  // The current status applies one more visit per discipline at its last scheduled date, without counting it.
  let probes = [Visit(date: thru[0], discipline: "PT", units: 1),
                Visit(date: thru[1], discipline: "OT", units: 1),
                Visit(date: thru[2], discipline: "ST", units: 1)]
  let probed = process_visits(t: t,
                              visits: probes,
                              days: [],
                              limits: scheduled.limits,
                              mock: true)
  let current_status = status_map(probed.statuses)

  let case_sets = filter(t.case_payer_sets, c => c.patient_case == pc.id && is_some(c.payer_set))
  let set_ids = set_of(map(case_sets, c => unwrap_or(c.payer_set, 0)))
  let sequenced = filter(t.sequences,
                         q => set_has(set_ids, q.payer_set) && is_some(q.resident_payer))
  let from_sequences = set_of(map(sequenced, q => unwrap_or(q.resident_payer, 0)))
  let from_probes = set_of(map(filter(probed.payers, p => is_some(p)), p => unwrap_or(p, 0)))
  let active = if set_size(from_sequences) > 0 then from_sequences else from_probes
  let current = map(filter(scheduled.limits,
                           l => set_size(active) == 0 || set_has(active, l.resident_payer)),
                    l => view(l))
  return AuthorizationCheck(patient_case: pc.id,
                            current_status: current_status,
                            current: current,
                            all: map(scheduled.limits, l => view(l)),
                            summary: summary(current_status, current))
}
