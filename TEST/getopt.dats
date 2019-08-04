#include "share/HATS/temptory_staload_bucs320.hats"

#staload "./../SATS/vcopyenv.sats"
#staload "./../SATS/strbuf.sats"
#staload _ = "./../DATS/strbuf.dats"
#staload _ = "./../DATS/pointer.dats"

#staload "./../SATS/getopt.sats"
#staload
_ = "./../DATS/getopt.dats"

(* ****** ****** *)

fun{}
stropt_get_opt (x: stropt, d: string): string = let
  var w : ptr
  val opt = $UN.castvwtp0{[n:int]stropt(n)}(x)
in
  if stropt_get (opt, w) then let
    prval () = opt_unsome(w)
    val res = w
    prval () = topize(w)
  in
    res
  end else let prval () = opt_unnone(w) in d end
end


implfun
main1 (argc, argv) = let
//
var key_long = stropt0_none()
prval pf_key_long = view@ key_long
var key_short = '\0' : char
prval pf_key_short = view@ key_short
//
//
impltmp{}
error_missing_param () = let
  prval (pf_long, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_key_long))
  prval (pf_short, fpf2) = vcopyenv_v_decode ($vcopyenv_v (pf_key_short))
  val key = stropt_get_opt (key_long, "")
  val c = key_short
  val () = print!("please supply the required parameter for option ")
  val () =
  (
    if key = "" then print!("-", c)
    else print!("--", key)
  )
  prval () = fpf1 (pf_long)
  prval () = fpf2 (pf_short)
  val _ = exit(1)
in
  
end
//
impltmp{}
long_has_param (key) =
  if key = "help" || key = "foobar" || key = "baz" then (print!("long([", key, "])"); false)
  else let
    prval (pf_long, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_key_long))
    val () = key_long := stropt0_some (key)
    prval () = fpf (pf_long)
  in
    true
  end
impltmp{}
short_has_param (key) =
  if key = 'h' || key = 'x' || key = 'z' || key = 'b' then (print!("short([", key, "])"); false)
  else let
    prval (pf_short, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_key_short))
    val () = key_short := key
    prval () = fpf (pf_short)    
  in
    true
  end
//
impltmp{}
handle_positional (num, arg) =
  print!("positional(", num, ", [", arg, "])")
impltmp{}
handle_param(value) = let
  prval (pf_long, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_key_long))
  prval (pf_short, fpf2) = vcopyenv_v_decode ($vcopyenv_v (pf_key_short))
  val key = stropt_get_opt (key_long, "")
  val c = key_short
  val () =
    if c != '\0' then print!("short([", c, "], [", value, "])")
    else if key != "" then print!("long([", key, "], [", value, "])")
    else assertloc(1 = 0) // shouldn't really happen!
  prval () = fpf1 (pf_long)
  prval () = fpf2 (pf_short)
in
end
//
val () = assertloc(argc >= 1)
//
val () = parse_args (1, argc, argv)
val () = println!()
//
prval () = view@ key_long := pf_key_long
prval () = view@ key_short := pf_key_short
//
in
0
end
