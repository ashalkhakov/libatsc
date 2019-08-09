// NOTE: these are user-provided

// called when the option is non-flag but there
// was not any parameter specified
fun{}
error_missing_param (): void

// return [true] if given option is requires a parameter
// return [false] if it is argless (and work on it right away)
// throw if this option is unknown
fun{}
long_has_param (key: string): bool
fun{}
short_has_param (key: char): bool

// handle parameter to option
fun{}
handle_param (value: string): void

// [num] is the num-th positional argument
// [rest] is the [argv] subarray where [rest.[0]] is the argument
// [i] is the index in the original [argv]
// return [true] if consumed all of [rest], not just the first element
fun{}
handle_positional {n:pos} (
  num: int
, rest: &(@[string][n])
, num_rest: size n
, i: int
): bool

(** lang=markdown

Parse arguments, invoking one of the handling functions.

The grammar is roughly as follows.

Terminals:

````
alphanumeric := ['a'-'z' 'A'-'Z' '0'-'9']
end_of_opts := "--"
short_option := "-" alphanumeric
short_options := short_option alphanumeric*
long_option := "--" alphanumeric+
parameter := [^ '-' ] . *
````

Non-terminals:

````
args ::= option* end_of_opts? positional*
option ::= short_option argument* // well, we will always take as many as we can
option ::= long_option argument* // again, take as many as you can
option ::= short_options
positional ::= argument*
````

Notes:

* if an option is followed by one or more parameters, then for each
  parameter, the function `handle_param_long` or `handle_param_short`
  (depending on whether the option is in short form or the long form)
  is invoked

* if an option is NOT followed by a parameter, then the function
  `handle_long` or `handle_short` is invoked

* for every positional parameter the function `handle_positional` is
  invoked, passing in the serial number of the positional parameter
  (starting at 0) and the parameter as-is

*)
fun{}
parse_args {n:pos}{i:nat | i <= n} (
  first: int(i),
  argc: int(n),
  argv: !argv(n)
): void
