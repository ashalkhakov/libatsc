
datatype
opt_arity
= OAnull // no argument
| OArequired // one argument is required
typedef
opt_handler = (stropt) -> void

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

fun
add_positional {l:addr} (
  cmd_pos0? @ l | ptr l, int, string, pos_handler, string
) : void

fun
parse {n:pos}{i:nat | i <= n} (
  first: int(i),
  argc: int(n),
  argv: !argv(n)
): void

fun
print_help (arg0: string): void
