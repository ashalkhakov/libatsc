#staload "libats/SATS/char.sats"
#staload "libats/SATS/gint.sats"
#staload "libats/SATS/gptr.sats"
#staload "libats/SATS/array.sats"
#staload "libats/SATS/string.sats"

#staload "./../SATS/array_prf.sats"

#staload
"./../SATS/strbuf.sats"
#staload
LIBC_STRING = "./../SATS/libc_string.sats"

#staload
"./../SATS/pointer.sats"

#staload
UN = "libats/SATS/unsafe.sats"

impltmp{}
strbuf_of_bytes {l,m} (pf | p) = let
//
prval (pf_at, pf1) = array_v_uncons{byte?}(pf)
//
prval () = char_byte_samesize ()
prval pf_at = char_byte_convert (pf_at)
//
val () = $effmask_wrt (!p := $UN.castvwtp0{char(0)}(0))
prval pf_sbf = strbuf_v_null (pf_at, pf1)
//
in
  (pf_sbf | ())
end

impltmp
{}(*tmp*)
strbuf_of_substring
  {bsz} {n} {st,ln} {l} (
  pf
| p, str, st, ln
) = {
//
var str = str
val (pf_str | p_str) = takeout (str)
//
prval pf' = c0hars_of_b0ytes_v (pf)
prval (pf1, pf2) = array_v_split_at (pf' | ln)
//  
prval (pf_str_pre, pf_str_rest) = strbuf_v_split_at (pf_str, st)
prval (pf_substr, pf_str_rest) = strbuf_v_split (pf_str_rest)
//  
val p_str_rest = ptr1_add<char> (p_str, st)
val lnb = ln*sizeof<char>
prval pf1 = __trustme (pf1) where {
  extern
  prfun __trustme {n:int}{l:addr} (array_v(char?,l,n)): array_v(c1har?,l,n)
}
val (pf_substr1, pf1_chars1 | _) =
  $LIBC_STRING.memcpy_tflt (pf_substr, pf1 | p, p_str_rest, lnb)
//  
val p_end = ptr1_add<char> (p, ln)
prval (pf21_at, pf211) = array_v_uncons {char?} (pf2)
prval () = char_byte_samesize ()
val () = !p_end := '\0'
//
prval pf2111 = b0ytes_of_c0hars_v (pf211)
prval pf_sbf = strbuf_v_null (pf21_at, pf2111)
prval pf_sbf = strbuf_v_unsplit (pf1_chars1, pf_sbf)
//  
prval pf_str_rest = strbuf_v_unsplit (pf_substr1, pf_str_rest)
prval pf_str = strbuf_v_unsplit (pf_str_pre, pf_str_rest)  
prval () = restore (pf_str, str)
//
prval () = pf := pf_sbf
//
} (* end of [strbuf_of_substring] *)

impltmp
{}(*tmp*)
strbuf_of_string
  {bsz} {n} {l} (
  pf
| p, str, n
) = {
//
prval () = __trustme (n) where {
  extern praxi __trustme {i:int} (size i): [i>=0] void
}
val () = strbuf_of_substring (pf | p, str, i2sz 0, n)
//
} (* end of [strbuf_of_string] *)

impltmp
{}(*tmp*)
strbuf_get_char_at {m,n} {i} (
  sbf, i
) = c where
{
//
val p_sbf = addr@ sbf
val p = ptr1_add<char> (p_sbf, i)
//
prval (pf_sbf_pre, pf_sbf_rest) = strbuf_v_split_at (view@ sbf, i)
prval (pf_i, pf_opt) = strbuf_v_uncons (pf_sbf_rest)
val c = !p
prval strbufopt_v_some (pf_sbf_rest) = pf_opt
prval pf_sbf_rest = strbuf_v_cons (pf_i, pf_sbf_rest)
//
prval () = lemma_strbuf_v_param (pf_sbf_rest)
prval () = view@ sbf := strbuf_v_unsplit (pf_sbf_pre, pf_sbf_rest)
//
}

impltmp
{}(*tmp*)
strbuf_set_char_at
  {m,n}
  {i} (
  sbf, i, c
) =
{
//
val p_sbf = addr@ sbf
val p = ptr1_add<char> (p_sbf, i)
//
prval (pf_sbf_pre, pf_sbf_rest) = strbuf_v_split_at (view@ sbf, i)
prval (pf_i, pf_opt) = strbuf_v_uncons (pf_sbf_rest)
val () = $effmask_wrt (!p := c)
prval strbufopt_v_some (pf_sbf_rest) = pf_opt
prval pf_sbf_rest = strbuf_v_cons (pf_i, pf_sbf_rest)
//
prval () = lemma_strbuf_v_param (pf_sbf_rest)
prval () = view@ sbf := strbuf_v_unsplit (pf_sbf_pre, pf_sbf_rest)
//
}

impltmp
{}(*tmp*)
strbuf_test_char_at_size {m,n}{i} (sbf, i) = let

  val p_sbf = addr@ sbf
  val p = ptr1_add<char> (p_sbf, i)
  
  prval (pf_sbf_pre, pf_sbf_rest) = strbuf_v_split_at (view@ sbf, i)
  prval (pf_i, pf_opt) = strbuf_v_uncons (pf_sbf_rest)
  val c = !p
  val res = (c = '\0')
  prval pf_sbf_rest = strbufopt_v_elim {m-i,n-i} (pf_i, pf_opt)

  prval () = lemma_strbuf_v_param (pf_sbf_rest)

  prval () = view@ sbf := strbuf_v_unsplit (pf_sbf_pre, pf_sbf_rest)
in
  $UN.castvwtp0{[c:uint | (c > 0 && i < n) || (c == 0 && i == n)] char c}(c)
end

(* ****** ****** *)

impltmp
{}
stropt_get {n} (s, res) = let
//
val p = $UN.castvwtp0{ptr}(s)
//
in
//
if iseqz(p) then let
  prval () = opt_none{string(n)}(res) in false
end else let
  val () = res := $UN.castvwtp0{string(n)}(s)
  prval () = opt_some{string(n)}(res)
in
  true
end
//
end // end of [stropt_get]

impltmp
{}(*tmp*)
string_tail{n}(s) = let
  val p = ptrof(s)
  val p1 = ptr0_add<char>(p, 1)
in
  $UN.castvwtp0{string(n-1)}(p1)
end

impltmp
{}(*tmp*)
string_test_at {n}{i} (s, i) = let
  val p = ptrof(s)
  val p_i = ptr0_add<char>(p, i)
  val p_ic = ptr2cptr(p_i)
  val c = $effmask_all ($UN.cptr0_get<char>(p_ic))
in
  $UN.castvwtp0{[c:uint | (c > 0 && i < n) || (c == 0 && i == n)] char c}(c)
end
