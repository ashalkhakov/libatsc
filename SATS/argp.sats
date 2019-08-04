(** lang=markdown

Parse arguments, invoking user-supplied handling functions.

With this module, user creates global variables for every command-line
option or positional argument that they intend to handle.

*)

datatype
opt_arity
= OAnull // no argument
| OArequired // one argument is required

(** lang=markdown

type for an option handler:

* if arity is `OAnull()`, then this handler is called with null `stropt`
* otherwise, this handler is called with a non-null `stropt`

*)
typedef
opt_handler = (stropt) -> void

/// command-line option
typedef cmd_opt (l:addr) = @{
  short_name= char      /// short name, or '\0' if not present
, long_name= stropt     /// long name, or null `stropt` if not present
, arity= opt_arity      /// how many parameters does this option take
, param_name= stropt    /// name of parameter (if this option takes a required parameter)
, handler= opt_handler  /// handling function
, help= string          /// human-readable help text
, next= ptr l           /// internal use
}
typedef cmd_opt0 = cmd_opt(null)

/// register an option handler
fun
add_option {l:addr} (
  cmd_opt0? @ l
| p: ptr l
, short: char
, long: stropt
, arity: opt_arity
, param_name: stropt
, handler: opt_handler
, help: string
) : void

typedef pos_handler = (string) -> void
typedef cmd_pos (l:addr) = @{
  index= int
, name= string
, handler= pos_handler
, help= string
, next= ptr l
}
typedef cmd_pos0 = cmd_pos(null)

/// register a positional argument handler
fun
add_positional {l:addr} (
  cmd_pos0? @ l | ptr l, int, string, pos_handler, string
) : void

/// parse arguments, starting at `first`
fun
parse {n:pos}{i:nat | i <= n} (
  first: int(i),
  argc: int(n),
  argv: !argv(n)
): void

/// print help message, listing all options and positional arguments
fun
print_help (arg0: string): void
