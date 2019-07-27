// NOTE: these are user-provided

// [arg] is [num]th positional arg
fun{}
handle_positional (num: int, arg: string): void
// [value] is parameter of [key]
fun{}
handle_param_long(key: string, value: string): void
// [key] is argless here
fun{}
handle_long(key:string): void
// [value] is parameter of [key]
fun{}
handle_param_short(key: char, value: string): void
// [key] is argless here
fun{}
handle_short(key: char): void

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
