#staload "libats/SATS/array.sats"
#staload "libats/SATS/gint.sats"
#staload "libats/SATS/gptr.sats"
#staload "libats/SATS/string.sats"
#staload "libats/SATS/stdio.sats"
#staload "libats/SATS/stropt.sats"

#staload
UN = "libats/SATS/unsafe.sats"

#staload "./../SATS/array_prf.sats"

#staload "./../SATS/strbuf.sats"
#staload "./../SATS/pointer.sats"

#staload "./../SATS/getopt.sats"

(* ****** ****** *)

datatype
toktype = tt_end_of_opts | tt_short | tt_long | tt_param | tt_eof
typedef
token = @{type= toktype, value= string, cvalue= char}
vtypedef
tokenizer (n:int) = [i:nat | i <= n] @{
  pos=int i
, argc= int n
, argv=argv(n)
, long=bool
, opt= stropt
} (* end of [tokenizer] *)

(* ****** ***** *)

extern
fun{}
get_token{n:int}(&tokenizer(n) >> _, &token? >> token): void

impltmp
{}(*tmp*)
get_token{n}(tr, res) = let
//
var w : ptr
val opt = $UN.castvwtp0{[n:int]stropt(n)}(tr.opt)
//
in
//
if stropt_get(opt, w) then let // have an option's parameter already
  prval () = opt_unsome(w)
in
  if tr.long then let // it was a long option
    val () = tr.opt := stropt0_none()
    val () = (
      res.type := tt_param();
      res.value := w;
      res.cvalue := '\0'
    )
    prval () = topize(w)
  in
  end else (*short*) let
    val opts = w
    prval () = topize(w)
    prval () = lemma_string_param (opts)
    val c = string_test_at(opts, i2sz 0)
  in
    if c = '\0' then let
      val () = tr.opt := stropt0_none ()
    in
      get_token(tr, res)
    end else let
      val () = (
        res.type := tt_short();
        res.value := "";
        res.cvalue := c
      )
      val opts = string_tail (opts)
      val () = tr.opt := stropt0_some (opts)
    in
    end
  end
end else let
  prval () = opt_unnone(w)
in
//
if tr.pos = tr.argc then (
  res.type := tt_eof();
  res.value := "";
  res.cvalue :='\0';
  tr.opt := stropt0_none()
) else let
  val arg = argv_get_at (tr.argv, tr.pos)
  val arg = (g1ofg0)arg
  val c0 = string_test_at(arg, i2sz 0)
in
  if c0 = '-' then let // option?
    val arg = string_tail arg
    val c1 = string_test_at (arg, i2sz 0)
  in
    if c1 = '-' then let // long option or end of options?
      val arg = string_tail arg
      val c2 = string_test_at (arg, i2sz 0)
    in
      // end of options
      if c2 = '\0' then let
      in
        tr.opt := stropt0_none();
        res.type := tt_end_of_opts();
        res.value := arg;
        res.cvalue := '\0';
        tr.pos := succ(tr.pos)
      end else let // long, but look for '='!
        var argp = arg
        val (pf_strbuf | p_strbuf) = string_takeout_strbuf (argp)
        val () = assertloc(ptr1_isneqz(p_strbuf))
        val (pf_strchr | p_strchr) = strbuf_strchr (pf_strbuf | p_strbuf, '=')
        prval () = ptr_lemma (p_strchr) where {
          extern
          praxi ptr_lemma {l:addr} (p: ptr l) : [l>=null] void
        }
        val () =
          if :(argp: string) => ptr1_isneqz (p_strchr) then let
            //
            prval (pf_chars, pf_at, pf_sopt) = strchr_v_unsome (pf_strchr)
            prval strbufopt_v_some (pf_aft) = pf_sopt
            val p_aft = ptr1_add<char>(p_strchr, i2sz 1)
            val () = ptr_write0 (pf_at | p_strchr, '\0')
            prval pf_chars0 =
              strbuf_v_restore (pf_chars, pf_at, array_v_nil{byte?}())
            //
            extern
            castfn
            string_of_strbuf {m,n:int}{l:addr} (
              strbuf_v(m,n,l) | ptr l
            ) : string(n)
            //
            val () = tr.opt := stropt0_some(string_of_strbuf(pf_aft | p_aft));
            val value = string_of_strbuf (pf_chars0 | p_strbuf)
            val () = (
              res.type := tt_long();
              res.value := value;
              res.cvalue := '\0';
            )
            val () = tr.long := true
            val () = tr.pos := succ(tr.pos)
            //
            prval () = __alright (argp) where {
              extern
              praxi __alright {n:int}{l:addr} (
                !stringptrout(n,l) >> string n
              ): void
            }
            //
          in
          end else let
            //
            prval (pf_sbf) = strchr_v_unnone (pf_strchr)
            prval () = pf_strbuf := pf_sbf
            prval () = string_restore_strbuf (pf_strbuf, argp)
            //
          in
            //
            // NOTE: '=' is not found!
            //
            res.type := tt_long();
            res.value := argp;
            res.cvalue := '\0';
            tr.pos := succ(tr.pos)            
          end
        //
      in
      end // end of [else]
    end else let // short option
      val opt = arg
      val rest =
        if string_test_at (opt, i2sz 0) = '\0' then stropt0_none ()
        else stropt0_some (string_tail opt)
    in
      res.type := tt_short();
      res.value := arg;
      res.cvalue := c1;
      tr.opt := rest;
      tr.long := false;
      tr.pos := succ(tr.pos);
    end
  end else let
  in
    tr.opt := stropt0_none();
    res.type := tt_param();
    res.value := arg;
    res.cvalue := '\0';
    tr.pos := succ(tr.pos)
  end
end
//
end
//
end

(* ****** ****** *)

impltmp{}
parse_args {n}{i} (i, argc, argv) = let
//
fnx
args(tr : &tokenizer(n) >> _, tok : &token): void =
(
case+ tok.type of
| tt_eof() => () // eof!
| tt_short() => collect_short(tok.cvalue, 0, tr)
| tt_long() => collect_long(tok.value, 0, tr)
| tt_end_of_opts () => let
    val i = tr.pos
  in
    if i < tr.argc then positional (0, tr, i)
  end
| tt_param () => let
    val i = tr.pos - 1
  in
    if i >= 0 then (
      if i < tr.argc then {
        // reuse this token if it was a --key=value kind of option
        val tmp = argv_get_at (tr.argv, i)
        val rp = (ptrof(tmp) != ptrof(tok.value))
        val () = if rp then argv_set_at (tr.argv, i, tok.value)
        val () = positional (0, tr, i)
      }
    )
  end
)
//
and collect_short(opt: char, count: int, tr: &tokenizer(n) >> _): void =
let
  var tok: token
  val () = get_token(tr, tok)
in
  if short_has_param (opt) then (
    case+ tok.type of
    | tt_param() => {
      val () = handle_param(tok.value)
      prval () = topize (tok)
      val () = get_token (tr, tok)
      val () = args(tr, tok)
    }
    | _ => (
      error_missing_param ();
      args (tr, tok)
    )
  ) else args (tr, tok)
end
//
and collect_long(opt: string, count: int, tr: &tokenizer(n) >> _): void =
let
  var tok: token
  val () = get_token(tr, tok)
in
  if long_has_param (opt) then (
    case+ tok.type of
    | tt_param() => {
      val () = handle_param (tok.value)
      prval () = topize (tok)
      val () = get_token (tr, tok)
      val () = args(tr, tok)
    }
    | _ => (
      error_missing_param ();
      args (tr, tok)
    )
  ) else args (tr, tok)
end
//
and positional {i:nat | i < n} (num: int, tr: &tokenizer(n) >> _, i: int(i)): void = let
//  
  extern
  castfn
  argv_takeout {n:int}(
    !argv(n)
  ):<> [l:addr] (
    array_v(string,l,n), array_v(string,l,n) -<lin,prf> void
  | ptr(l)
  )
//
  val (pf_arr, fpf | p_arr) = argv_takeout (tr.argv)
  val idx = i2sz i
  prval (pf1_arr, pf2_arr) = array_v_split_at (pf_arr | idx)
  val p2_arr = ptr1_add<string> (p_arr, idx)
  // tok is the num-th positional argument!
  val sz = tr.argc - i
  val consumed_rest = handle_positional (num, !p2_arr, i2sz sz, i)
  prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
  prval () = fpf (pf_arr)
//  
in
  if consumed_rest then ()
  else let
    val i = succ(i)
  in
    if i < tr.argc then {
      val num = succ(num)
      val () = positional (num, tr, i)
    }
  end
end
//
prval () = lemma_argv_param (argv)
//
var tr =
  @{pos= i, argc=argc, argv=argv, long=false, opt= stropt0_none()}
   : tokenizer(n)
var tok: token
val () = get_token (tr, tok)
val () = args (tr, tok)
//
prval () = topize(tr.opt)
prval () = argv := tr.argv
//
in
end
