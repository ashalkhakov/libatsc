#staload
"libats/SATS/gint.sats"
#staload
_ = "libats/DATS/gint.dats"
#staload
"libats/SATS/gptr.sats"
#staload
_ = "libats/DATS/gptr.dats"
#staload
"libats/SATS/gref.sats"
#staload
_ = "libats/DATS/gref.dats"
#staload
"libats/SATS/print.sats"
#staload
_ = "libats/DATS/print.dats"
#staload
"libats/SATS/char.sats"
#staload
_ = "libats/DATS/char.dats"
#staload
"libats/SATS/string.sats"
#staload
_ = "libats/DATS/string.dats"
#staload
"libats/SATS/stropt.sats"
#staload
_ = "libats/DATS/stropt.dats"
#staload
IO = "libats/SATS/stdio.sats"
#staload
_ = "libats/DATS/stdio.dats"
#staload
UN = "libats/SATS/unsafe.sats"

#staload
"./../SATS/argp.sats"

#staload
"./../SATS/vcopyenv.sats"
#staload
"./../SATS/pointer.sats"
#staload
_ = "./../DATS/pointer.dats"
#staload "./../SATS/strbuf.sats"
#staload
_ = "./../DATS/strbuf.dats"
#staload
"./../SATS/slist.sats"
#staload _ = "./slist.dats"
#staload
"./../SATS/getopt.sats"
#staload
_ = "./../DATS/getopt.dats"

dataview
optn1_view_bool_view
(
  a:view, bool
) =
  | optn1_v_none(a, ff)
  | optn1_v_some(a, tt) of (a)
sexpdef optn1_v = optn1_view_bool_view
sexpdef optn1_v(a:vtflt) = [b:bool] optn1_v(a, b)

extern
castfn
ref_takeout {a:vtflt}
(ref(a)):<> [l:agz] (a @ l, a @ l -<lin,prf> void | ptr l)

impltmp
slist_node_get_next<cmd_opt> {l1,l2} (pf_v | p) = !p.next
impltmp
slist_node_set_next<cmd_opt> {l1,l2,l3} (pf_v | p, n) = !p.next := n

vtypedef optionlist = slist0 (cmd_opt)
var options = slist_nil<cmd_opt> () : optionlist
val the_options = ref_make_viewptr (view@ options | addr@ options)

val p_options = addr@ options

impltmp
slist_node_get_next<cmd_pos> {l1,l2} (pf_v | p) = !p.next
impltmp
slist_node_set_next<cmd_pos> {l1,l2,l3} (pf_v | p, n) = !p.next := n

vtypedef positionallist = slist0 (cmd_pos)
var positionals = slist_nil<cmd_pos> () : positionallist
val the_positionals = ref_make_viewptr (view@ positionals | addr@ positionals)

val p_positionals = addr@ positionals

implfun
add_option {l} (
  pf_at | p, short, long, arity, param_name, handler, help
) = {
  val () = (
    !p.short_name := short;
    !p.long_name := long;
    !p.arity := arity;
    !p.param_name := param_name;
    !p.handler := handler;
    !p.help := help;
    !p.next := the_null_ptr
  )
  
  val (vbox pf_list | p_list) = ref_vptrof {optionlist} (the_options)
  val () = $effmask_all (slist_cons<cmd_opt> (pf_at | !p_list, p))
}

implfun
add_positional {l} (
  pf_at | p, idx, name, handler, help
) = {
  val () = (
    !p.index := idx;
    !p.name := name;
    !p.handler := handler;
    !p.help := help;
    !p.next := the_null_ptr
  )
  val (vbox pf_list | p_list) = ref_vptrof {positionallist} (the_positionals)
  val () = $effmask_all (slist_cons<cmd_pos> (pf_at | !p_list, p))
}

(* ****** ****** *)

abstbox h_opt (addr) = ptr
typedef h_opt0 = [l:addr] h_opt(l)

extern
fun{}
h_opt_null (): h_opt(null)
extern
fun{}
h_opt_is_null {l:addr} (h_opt(l)): bool (l == null)
extern
fun{}
h_opt_is_some {l:addr} (h_opt(l)): bool (l > null)
extern
fun{}
h_opt_lookup_short (c: char, &slist0(cmd_opt)): [l:addr] h_opt(l)
extern
fun{}
h_opt_lookup_long (s: string, &slist0(cmd_opt)): [l:addr] h_opt(l)
extern
castfn
h_opt_decode {l:agz} (h_opt(l)): [l1:addr] (
  cmd_opt(l1) @ l, cmd_opt(l1) @ l -<lin,prf> void
| ptr l
)

impltmp{}
h_opt_null () = $UN.castvwtp0{h_opt(null)}(the_null_ptr)

impltmp{}
h_opt_is_null {l:addr} (p) =
  $UN.castvwtp0{bool(l == null)}(ptr0_iseqz ($UN.castvwtp0{ptr}(p)))
impltmp{}
h_opt_is_some {l:addr} (p) =
  $UN.castvwtp0{bool(l > null)}(ptr0_isneqz ($UN.castvwtp0{ptr}(p)))

impltmp{}
h_opt_lookup_long (key, list) = let
  val (pf_opt | p_opt) = slist_search_takeout<cmd_opt>(list)
  where {
    impltmp
    slist_search$pred<cmd_opt> (x) =
      g0eq_stropt_stropt (x.long_name, stropt0_some(key))
  }
in
  if ptr1_isneqz p_opt then let
    prval vtakeout_some_v (pf_at, fpf) = pf_opt
    val res = $UN.castvwtp0{[l:agz]h_opt(l)}(p_opt)
    prval () = fpf (pf_at)
  in
    res
  end else let
    prval vtakeout_none_v () = pf_opt
  in
    h_opt_null ()
  end
end

impltmp{}
h_opt_lookup_short (key, list) = let
  val (pf_opt | p_opt) = slist_search_takeout<cmd_opt>(list)
  where {
    impltmp
    slist_search$pred<cmd_opt> (x) =
      (x.short_name = key)
  }
in
  if ptr1_isneqz p_opt then let
    prval vtakeout_some_v (pf_at, fpf) = pf_opt
    val res = $UN.castvwtp0{[l:agz]h_opt(l)}(p_opt)
    prval () = fpf (pf_at)
  in
    res
  end else let
    prval vtakeout_none_v () = pf_opt
  in
    h_opt_null ()
  end
end

(* ****** ****** *)

fun{}
run_positional (num: int, arg: string, list: &slist0(cmd_pos)): void = let
  val (pf_opt | p_opt) = slist_search_takeout<cmd_pos>(list)
  where {
    impltmp
    slist_search$pred<cmd_pos> (x) = (x.index = num)
  }
in
  if ptr1_isneqz p_opt then {
    prval vtakeout_some_v (pf_at, fpf) = pf_opt
    val () = !p_opt.handler (arg)
    prval () = fpf (pf_at)
  } else {
    prval vtakeout_none_v () = pf_opt
    // FIXME: error handling?
    val () = println!("unknown positional argument number: ", num)
    val () = assert_errmsg(1 = 0, "unable to parse")
  }
end

(* ****** ****** *)

extern
fun{}
print_usage (
  arg0: string, options: &slist0(cmd_opt), positionals: &slist0(cmd_pos)
): void

impltmp{}
print_usage (arg0, options, positionals) = {
//
// Usage: <arg0> [-h] [-o FILE] [-i[=FILE]] ARG...
//
val () = print!("Usage: ", arg0)
//
val () = (slist_foreach<cmd_opt> (options)) where
{
  impltmp
  slist_foreach$work<cmd_opt> (x) = {
    val () = print!(" ")
    val () = print!("[")
        
    val () = if iseqz(x.short_name)
      then print!("-", x.short_name)
      else print!("--", x.long_name)
        
    val param_name = (let
      var w : ptr
      val opt = $UN.castvwtp0{[n:int]stropt(n)}(x.param_name)
    in
      if stropt_get (opt, w) then let
        prval () = opt_unsome (w)
        val res = w
        prval () = topize(w)
      in
        (g0ofg1)res
      end else let prval () = opt_unnone (w) in (g0ofg1)"ARG" end
    end) : string

    val () =
      case+ x.arity of
      | OAnull () => ()
      | _ => print!('=', param_name)

    val () = print!("]")
  }
}
//
val () = slist_foreach<cmd_pos> (positionals) where
{
  impltmp
  slist_foreach$work<cmd_pos> (x) =
  {
    val () = print!(" ")
    val () = print!(x.name)
  }
}
//
}

extern
fun{}
print_help_text (x: string): void

extern
fun{}
print_help_options (&slist0 (cmd_opt)): void

impltmp{}
print_help_options (options): void = {
//
val () = slist_foreach<cmd_opt> (options) where
{
  // "Usage: <arg0> [OPTION...] ARG...
  // ""
  // "Options:"
  // ""
  // "  -h|--help          print help" // null arg
  // "  -o|--output=FILE   specify output file" // required arg
  impltmp
  slist_foreach$work<cmd_opt> (x) = {
    val () = print!("  ")
    
    val has_short = isneqz(x.short_name)
    val () = if has_short then print!('-', x.short_name)
    
    val () = (let
      var w : ptr
      val opt = $UN.castvwtp0{[n:int]stropt(n)}(x.long_name)
    in
      if stropt_get (opt, w) then let
        prval () = opt_unsome (w)
        val long_name = w
        val () = if has_short then print!('|')
        val () = print!("--", long_name)
        prval () = topize(w)
      in
      end else let prval () = opt_unnone (w) in () end
    end)
    
    val () =
      case+ x.arity of
      | OAnull() => ()
      | OArequired () => print!("=ARG")

    val () = print_help_text(x.help)
  }
}
//
}

implfun
print_help (arg0) =
{
val (pf_options, fpf_options | p_options) = ref_takeout {optionlist} (the_options)
val (pf_positionals, fpf_positionals | p_positionals) = ref_takeout {positionallist} (the_positionals)

val () = print_usage(arg0, !p_options, !p_positionals)
val () = print_newline ()
val () = println!("Options:")

prval () = fpf_options (pf_options)
prval () = fpf_positionals (pf_positionals)

// minimum distance between the end of first column
// and the beginning of the second column
val rpad = 4

// first pass, compute maximum indent for the second column;
// do not print as of yet!
val max_indent = let
  var indent = (g0ofg1)0
  prval pf_indent = view@ indent
  var max_indent = (g0ofg1)0
  prval pf_max_indent = view@ max_indent

  impltmp
  print_newline<>() = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    prval (pf2_at, fpf2) = vcopyenv_v_decode ($vcopyenv_v (pf_max_indent))
  
    val o_max = max_indent
    val n_max = indent
    
    val x = (if o_max < n_max then n_max else o_max)
    val () = max_indent := x
    val () = indent := 0
    prval () = fpf1 (pf1_at)
    prval () = fpf2 (pf2_at)
  }
  impltmp
  print_char<> (c) = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val i = indent
    val () = indent := i+1
    prval () = fpf1 (pf1_at)
  }
  impltmp
  print_string<> (s) = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val l = string1_length((g1ofg0)s)
    val i = indent
    val () = indent := i+l
    prval () = fpf1 (pf1_at)
  }
  impltmp
  print_help_text<> (x) = print_newline ()

  val (pf_options, fpf_options | p_options) = ref_takeout {optionlist} (the_options)
  val () = print_help_options (!p_options)
  prval () = fpf_options (pf_options)

  val res = max_indent
  prval () = view@ indent := pf_indent
  prval () = view@ max_indent := pf_max_indent
in
  res
end

// second pass: print almost normally, but increase the local
// indent as necessary, then pad
val () = {
  var indent = (g0ofg1)0
  prval pf_indent = view@ indent

  impltmp
  print_newline<>() = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val () = indent := 0
    prval () = fpf1 (pf1_at)
    val () = $IO.fprint_newline<>($IO.the_stdout<>())
  }
  impltmp
  print_char<> (c) = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val i = indent
    val () = indent := i+1
    prval () = fpf1 (pf1_at)
    val () = $IO.fprint$val<char>($IO.the_stdout<>(), c)
  }
  impltmp
  print_string<> (s) = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val l = string1_length((g1ofg0)s)
    val i = indent
    val () = indent := i+l
    prval () = fpf1 (pf1_at)
    val () = $IO.fprint$val<string>($IO.the_stdout<>(), s)
  }
  //
  fun
  pad (c: char, i:int): void =
    if i <= 0 then ()
    else (print_char(c); pad (c, i-1))
  //
  impltmp
  print_help_text<> (x) = {
    prval (pf1_at, fpf1) = vcopyenv_v_decode ($vcopyenv_v (pf_indent))
    val i = indent
    prval () = fpf1 (pf1_at)
    val max = max_indent
    
    val () = pad (' ', max-i+rpad)
    val () = println!(x)
  }
  val (pf_options, fpf_options | p_options) = ref_takeout {optionlist} (the_options)
  val () = print_help_options (!p_options)
  prval () = fpf_options (pf_options)
  prval () = view@ indent := pf_indent
}
//
}

(* ****** ****** *)

implfun
parse {n}{i} (first, argc, argv) = {
//
var last_node = h_opt_null() : h_opt0
prval pf_last_node = view@ last_node
//
impltmp{}
error_missing_param () = {
  prval (pf_node, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_last_node))
  val () = assert(h_opt_is_some(last_node))
  val (pf_at, fpf_at | p) = h_opt_decode (last_node)

  val () = print!("please supply the required parameter for option ")
  
  val has_short = isneqz(!p.short_name)
  val () = if has_short then print!('-', !p.short_name)
    
  val () = (let
    var w : ptr
    val opt = $UN.castvwtp0{[n:int]stropt(n)}(!p.long_name)
  in
    if stropt_get (opt, w) then let
      prval () = opt_unsome (w)
      val long_name = w
      val () = if has_short then print!('|')
      val () = print!("--", long_name)
      prval () = topize(w)
    in
    end else let prval () = opt_unnone (w) in () end
  end)
  val () = print_newline ()

  prval () = fpf_at (pf_at)
  prval () = fpf (pf_node)
  val _ = exit(1)
}
//
impltmp{}
long_has_param (key) = let
  val (pf_options, fpf_options | p_options) =
    ref_takeout {optionlist} (the_options)
  prval (pf_node, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_last_node))
  val res = h_opt_lookup_long (key, !p_options)
  // otherwise it's an unknown option and we should fail
  val () = assert(h_opt_is_some (res))
  val (pf_at, fpf_at | p) = h_opt_decode (res)
  val has_param =
    case+ !p.arity of
    | OArequired() => true
    | _ => (!p.handler (stropt0_none()); false)
  prval () = fpf_at (pf_at)
  val () = last_node := res
  prval () = __leak (pf_node, fpf) where {
    extern
    prfun __leak {v1,v2:view} (v1, v2): void
  }
  prval () = fpf_options (pf_options)
in
  has_param
end
impltmp{}
short_has_param (key) = let
  val (pf_options, fpf_options | p_options) =
    ref_takeout {optionlist} (the_options)
  prval (pf_node, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_last_node))
  val res = h_opt_lookup_short (key, !p_options)
  // otherwise it's an unknown option and we should fail
  val () = assert(h_opt_is_some (res))
  val (pf_at, fpf_at | p) = h_opt_decode (res)
  val has_param =
    case+ !p.arity of
    | OArequired() => true
    | _ => (!p.handler (stropt0_none()); false)
  prval () = fpf_at (pf_at)
  val () = last_node := res
  prval () = __leak (pf_node, fpf) where {
    extern
    prfun __leak {v1,v2:view} (v1, v2): void
  }
  prval () = fpf_options (pf_options)
in
  has_param
end
impltmp{}
handle_param (value) = {
  prval (pf_node, fpf) = vcopyenv_v_decode ($vcopyenv_v (pf_last_node))
  val () = assert(h_opt_is_some(last_node))
  val (pf_at, fpf_at | p) = h_opt_decode (last_node)
  
  val () = !p.handler(stropt0_some(value))

  prval () = fpf_at (pf_at)
  prval () = fpf (pf_node)
}
//
impltmp{}
handle_positional (num, arg) = {
  val (pf_positionals, fpf_positionals | p_positionals) =
    ref_takeout {positionallist} (the_positionals)
  val () = run_positional (num, arg, !p_positionals)
  prval () = fpf_positionals (pf_positionals)
}
//
val () = parse_args (first, argc, argv)
//
prval () = view@ last_node := pf_last_node
//
}

