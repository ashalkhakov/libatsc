(** lang=markdown

Parse arguments, invoking user-supplied handling functions.

With this module, user creates global variables for every command-line
option or positional argument that they intend to handle.

*)

/// option arity (i.e. number of parameters)
datatype
opt_arity
= OAnull      /// no parameters
| OArequired  /// one parameter is required

(** lang=markdown

type for an option handler:

* if arity is `OAnull()`, then this handler is called with null `stropt`
* otherwise, this handler is called with a non-null `stropt`

*)
typedef
opt_handler = (stropt) -> void

/// command-line option
typedef cmd_opt (l:addr) = @{
  short_name= char
, long_name= stropt
, arity= opt_arity
, param_name= stropt
, handler= opt_handler
, help= string
, next= ptr l
}
typedef cmd_opt0 = cmd_opt(null)

/// register an option handler
fun
add_option {l:addr} (
  cmd_opt0? @ l
| p: ptr l
, short: char           /// short name, or '\0' if not present
, long: stropt          /// long name, or null `stropt` if not present
, arity: opt_arity      /// how many parameters does this option take
, param_name: stropt    /// name of parameter (if this option takes a required parameter)
, handler: opt_handler  /// handling function
, help: string          /// human-readable help text
) : void

/// positional argument arity
datatype
pos_arity =
| PAsingle    /// single argument
| PAvariadic  /// consumes the rest of positional arguments

/// type for a positional argument handler
abstbox pos_handler = (ptr, size) -> void
typedef pos_handler_fn (n:int) = (&array(string, n), size n) -> void

castfn
pos_handler_intr (f: {n:pos} pos_handler_fn(n)): pos_handler
castfn
pos_handler_elim (pos_handler): {n:pos} pos_handler_fn(n)

/// positional argument
typedef cmd_pos (l:addr) = @{
  index= int
, name= string
, arity= pos_arity
, handler= pos_handler
, help= string
, next= ptr l
}
typedef cmd_pos0 = cmd_pos(null)

/// register a positional argument handler
fun
add_positional {l:addr} (
  cmd_pos0? @ l
| p: ptr l
, index: int            /// sequential index of argument, starting at 0
, name: string          /// name of argument (for printing in usage text)
, arity: pos_arity      /// arity of argument
, handler: pos_handler  /// handler
, help: string          /// human-readable help text
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
