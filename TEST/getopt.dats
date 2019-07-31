#include "share/HATS/temptory_staload_bucs320.hats"

#staload _ = "./../DATS/strbuf.dats"
#staload _ = "./../DATS/pointer.dats"

#staload "./../SATS/getopt.sats"
#staload
_ = "./../DATS/getopt.dats"

(* ****** ****** *)

implfun
main1 (argc, argv) = let
//
impltmp{}
error_missing_param_long (key) =
  (println!("please supply the required parameter for option --", key); exit(1))
impltmp{}
error_missing_param_short (key) =
  (println!("please supply the required parameter for option -", key); exit(1))
//
impltmp{}
long_is_flag (key) =
  (key = "help" || key = "foobar" || key = "baz")
impltmp{}
short_is_flag (key) =
  (key = 'h' || key = 'x' || key = 'z' || key = 'b')
//
impltmp{}
handle_positional (num, arg) =
  print!("positional(", num, ", [", arg, "])")
impltmp{}
handle_param_long(key, value) =
  print!("long([", key, "], [", value, "])")
impltmp{}
handle_long(key) =
  print!("long([", key, "])")
impltmp{}
handle_param_short(key, value) =
  print!("short([", key, "], [", value, "])")
impltmp{}
handle_short(key) = print!("short([", key, "])")
//
val () = assertloc(argc >= 1)
//
val () = parse_args (1, argc, argv)
val () = println!()
//
in
0
end
