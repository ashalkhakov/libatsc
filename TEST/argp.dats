#include "share/HATS/temptory_staload_bucs320.hats"

#include "./../mylibies.hats"

// re-open in this scope
#staload $ARGP
// inline the dats file
// to keep everything in one compilation unit of C
local #include "./../DATS/argp.dats" in end

var version : cmd_opt0
val () = add_option (
  view@ version
| addr@ version
,  'v'
, stropt0_some("version")
, OAnull ()
, stropt0_none()
, lam(_) => (println!("argp 0.0.1"); exit(0))
, "output version information and exit"
)

var help : cmd_opt0
val () = add_option (
  view@ help
| addr@ help
, 'h'
, stropt0_some("help")
, OAnull ()
, stropt0_none()
, lam(_) => print_help ("argp") // TODO: thread argc/argv?
, "display this help and exit"
)

var parents : cmd_opt0
val () = add_option (
  view@ parents
| addr@ parents
, 'p'
, stropt0_some("parents")
, OAnull ()
, stropt0_none()
, lam(_) => ()
, "no error if existing, make directories as needed"
)

var source : cmd_pos0
val () = add_positional (
  view@ source
| addr@ source
, 0
, "SOURCE"
, lam(x) => println!("source file: ", x)
, "source file"
)

var dest : cmd_pos0
val () = add_positional (
  view@ dest
| addr@ dest
, 1
, "DEST"
, lam(x) => println!("destination file: ", x)
, "destination file"
)

implement
main1 (argc, argv) = let
  val () = assertloc(argc>=1)
  val () =
    if argc=1 then print_help ("argp") else parse (1, argc, argv)
in
  0
end
