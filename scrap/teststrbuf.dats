#include
"share/atspre_staload.hats"

viewdef
strbuf_v(m:int,n:int,l:addr) = strbuf(m,n) @ l

typedef
c1har = [i:int | i > 0] char(i)
typedef
c1hars(n:int) = @[c1har][n]
viewdef
b0ytes_v(n:int,l:addr) = @[byte?][n] @ l
typedef
bytes(n:int) = @[byte][n]

extern
praxi strbuf_v_null
  {n:int} {l:addr} // [n] must be a nat
  (pf1: char 0 @ l, pf2: b0ytes (n) @ l + sizeof(char))
  : strbuf_v (n+1, 0, l)
// end of [strbuf_v]

extern
praxi strbuf_v_cons
  {m,n:int} {l:addr} // [m] and [n] must be nats
  (pf1: c1har @ l, pf2: strbuf_v (m, n, l + sizeof(char)))
  :<prf> strbuf_v (m+1, n+1, l)
// end of [strbuf_v_cons]

dataview
strbufopt_v (int, int, addr, int) =
  | {m:nat} {l:addr}
    strbufopt_v_none (m, ~1, l, 0) of b0ytes m @ l
  | {m,n:nat} {l:addr} {c:int | c <> 0}
    strbufopt_v_some (m, n, l, c) of strbuf_v (m, n, l)
// end of [strbufopt_v]

extern
prfun strbuf_v_unsplit
  {n1:nat}
  {m2,n2:nat}
  {l:addr} (
  pf_buf: c1hars n1 @ l, pf_str: strbuf_v (m2, n2, l+n1*sizeof(char))
) : strbuf_v (n1+m2, n1+n2, l)
// end of [strbuf_v_unsplit]

absview
strchr_v (int, int, int, addr,addr)

extern
praxi strchr_v_unnone : {c,m,n:int;l:addr} (strchr_v(c,m,n,l,null)) -<> strbuf_v(m,n,l)
extern
praxi strchr_v_unsome : {c,m,n:int;l:addr} {l1:agz} (strchr_v (c,m,n,l,l1)) -<> [i:nat | l1 == l+i*sizeof(char)] (
  c1hars i @ l
, char c @ l+i*sizeof(char)
, strbufopt_v (m-(i+1),n-(i+1),l+(i+1)*sizeof(char), c)
)

//extern
//prfun
//strchr_v_unnone {c,m,n:int;l:addr} (strchr_v(c,m,n,l,null)): strbuf_v (m,n,l)
(*
extern
prfun
strbuf_v_get_takeout {m,n:int;l:addr} (strbuf_v(m,n,l)): (
c1hars n @ l,
char 0 @ l+n*sizeof(char)
b0ytes_v(m-n, l+n*sizeof(char))
)
*)
extern
prfun
strbuf_v_restore {m,n:int;l:addr} (
  c1hars n @ l,
  char 0 @ l+n*sizeof(char),
  b0ytes_v(m,l+n*sizeof(char))
): strbuf_v(m+n, n, l)

extern
castfn
strnptr_of_strbuf_v {m,n:int;l:addr} (
  strbuf_v (m, n, l) | ptr l
) :<> (strnptr(l,n) -<lin,prf> strbuf_v (m, n, l) | strnptr(l,n))

extern
fun
strbuf_strchr {m,n:nat;c:int}{l:agz} (
  strbuf_v(m,n,l)
| ptr l, int c
): [l1:addr] (
  strchr_v (c, m, n, l, l1)
| ptr l1
) = "mac#strchr"


extern
fun{a:t0p}
ptr_read{l:addr}
  (pf: !INV(a) @ l | p: ptr l):<> a
implement{a}
ptr_read (pf | p) = !p

staload UN = "prelude/SATS/unsafe.sats"

fun
use_strchr {m,n:nat}{l:addr}(
  pf_sb: !strbuf_v(m,n,l) | p_sb: ptr l
): void = let
  val () = assertloc(p_sb > the_null_ptr)
  val c = g1ofg0($UN.castvwtp0{int}('='))
  //prval [c:int] EQINT() = eqint(c)
  val () = assertloc(c > 0)
  val (pf_strchr | p_strchr) = strbuf_strchr(pf_sb | p_sb, c)
  prval () = lemma_ptr_param (p_strchr)
  val () = println!("hmm")
in
  if p_strchr = the_null_ptr then let
    prval (pf) = strchr_v_unnone (pf_strchr)
    prval () = pf_sb := pf
    val () = println!("nothing found!")
  in
   
  end else let
    prval (pf_chars, pf_at, pf_sbufopt) = strchr_v_unsome pf_strchr
    prval strbufopt_v_some (pf_sbuf) = pf_sbufopt
   
    val () = println!("base ptr = ", p_sb)
    val () = println!("reading char at ", p_strchr)
   

    //val c = ptr_get<c1har> (pf_at | p_strchr)
    val c = ptr_read(pf_at | p_strchr) // !p_strchr
    val () = println!("here")
    val () = println!(c)
   
    val pp = ptr1_succ<char> (p_strchr)
    val (fpf | ps) = strnptr_of_strbuf_v (pf_sbuf | pp)
    val () = println!("there:")
    val () = println!(ps)
    prval pf_sbuf = fpf (ps)

    prval () = pf_sb := strbuf_v_unsplit (pf_chars, strbuf_v_cons (pf_at, pf_sbuf))
  in
  end
end

implement main0 () = let
//
val kv = "key=value"
//
var p_str with pf_str = @[char]('k','e','y','=','v','a','l','u','e','\0')
//val () = assertloc('\0' = p_str.[9])
//val () = assertloc(0 = $UN.castvwtp0{int}('\0'))
//val () = $extfcall(void, "strcpy", addr@ p_str, $UN.castvwtp0{ptr}(kv))
//val () = assertloc('k' = p_str.[0])
val () = println!($UN.castvwtp0{string}(addr@ p_str)) // this works!
//
val (pf_sbf, fpf | p_sbf) = oops(pf_str | addr@ p_str) where {
   extern
   castfn oops {n:pos} {l:addr} (array_v(char,l,n) | ptr l)
   : (strbuf_v(n,n-1,l), strbuf_v(n,n-1,l) -<lin,prf> array_v(char,l,n) | ptr l)
}
//
(*
    prval (pf_str1, fpf1) = strbuf_v_takeout_string (pf_sbf)
    val () = assertloc(p_sbf = addr@ p_str)
    val s = ptr_read(pf_str1 | p_sbf) // !p_str
    //val () = println!(kv) // this works!
    val () = assertloc(0 = $extfcall(int, "memcmp", kv, p_sbf, 10))
    val () = println!("full string:")
    //val () = println!(s) // fails here!
    // NOTE: there is something wrong with reading a [string] out of pointer!
    val () = println!($UN.castvwtp0{string}(p_sbf))
    prval pf_sbf = fpf1 (pf_str1)
*)
//
val () = use_strchr (pf_sbf | p_sbf)
//
prval () = pf_str := fpf (pf_sbf)
//
in
//
print"Hello World!\n"
//
end
