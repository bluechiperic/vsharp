// expect: TN3001 TN3007
module Strings

// s may be shorter than three characters.
fn head(s: String) -> String {
  return str_sub(s, 0, 3)
}

// The result is one character longer, not two.
fn shout(s: String) -> String
  ensures str_len(result) == str_len(s) + 2
{
  return "{s}!"
}
