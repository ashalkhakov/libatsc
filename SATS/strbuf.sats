
fun
g1eq_char_char
{i,j:uint}
( x: char i
, y: char j):<> bool (i == j) = "mac#temptory_g0eq_char_char"
#symload = with g1eq_char_char of 10

typedef bytes (n:int) = @[byte][n]
typedef b0ytes (n:int) = @[byte?][n]
viewdef bytes_v (l:addr, n:int) = array_v(byte, l, n)
viewdef b0ytes_v (l:addr, n:int) = array_v(byte?, l, n)

typedef chars (n:int) = @[char][n]
typedef c0hars (n:int) = @[char?][n]
typedef c1har = [c:uint8 | c > '\0'] char c
typedef c1hars (n:int) = @[c1har][n]

praxi char_byte_samesize (): [sizeof(char) == sizeof(byte)] void
praxi char_byte_convert {l:addr} (byte? @ l): char? @ l

prfun
c0hars_of_b0ytes_v {l:addr}{n:int} (b0ytes_v(l,n)):<prf> c0hars(n) @ l

prfun
b0ytes_of_c0hars_v {l:addr}{n:int} (c0hars(n) @ l):<prf> b0ytes_v(l, n)

abstflt strbuf(m:int,n:int) = @[char][m]

viewdef strbuf_v
  (m: int, n: int, l:addr) = strbuf (m, n) @ l
viewdef strbuf_v (l:addr) = [m,n:nat] strbuf (m, n) @ l

prfun
lemma_strbuf_v_param
{m,n:int}{l:addr}
(pf: !strbuf_v(m,n,l)): [m >= 0; n >= 0; m > n] void

praxi strbuf_v_null
  {n:int} {l:addr} // [n] must be a nat
  (pf1: char 0 @ l, pf2: b0ytes (n) @ l + sizeof(char))
  : strbuf_v (n+1, 0, l)
// end of [strbuf_v]

praxi strbuf_v_cons
  {m,n:int} {l:addr} // [m] and [n] must be nats
  (pf1: c1har @ l, pf2: strbuf_v (m, n, l + sizeof(char)))
  :<prf> strbuf_v (m+1, n+1, l)
// end of [strbuf_v_cons]

dataview
strbufopt_v (int, int, addr, int) =
  | {m:nat} {l:addr}
    strbufopt_v_none (m, ~1, l, 0) of b0ytes m @ l
  | {m,n:nat} {l:addr} {c:uint8 | c <> 0}
    strbufopt_v_some (m, n, l, c) of strbuf_v (m, n, l)
// end of [strbufopt_v]

praxi strbuf_v_uncons
  {m,n:int} {l:addr} (pf: strbuf_v (m, n, l))
  :<prf> [c:uint8] @(
   char c @ l, strbufopt_v (m-1, n-1, l + sizeof(char), c)
) // end of [strbuf_v_uncons]

praxi strbufopt_v_elim {m,n:int} {l:addr} {c:int} (
  char c @ l, strbufopt_v (m-1, n-1, l + sizeof(char), c)
) :<prf> strbuf_v (m, n, l)

(* ****** ****** *)

prfun strbuf_v_split
  {m,n:int}
  {i:nat | i <= n}
  {l:addr} (
 pf_str: strbuf_v (m, n, l)
) : (c1hars i @ l, strbuf_v (m-i, n-i, l+i*sizeof(char)))
// end of [strbuf_v_split]

prfun strbuf_v_split_at
  {m,n:int}
  {i:nat | i <= n}
  {l:addr} (
 pf_str: strbuf_v (m, n, l), i: size(i)
) : (c1hars i @ l, strbuf_v (m-i, n-i, l+i*sizeof(char)))
// end of [strbuf_v_split]

prfun
strbuf_v_takeout {m,n:int;l:addr} (
  strbuf_v(m,n,l)
): (
  c1hars n @ l
, char 0 @ l + n * sizeof(char)
, b0ytes_v(l + n * sizeof(char), m - n)
)

prfun
strbuf_v_restore {m,n:int;l:addr} (
  c1hars n @ l
, char 0 @ l+n*sizeof(char)
, b0ytes_v(l+n*sizeof(char), m)
): strbuf_v(m+n, n, l)

(* ****** ****** *)

absvtbox
stringptrout
(n:int, l:addr)

castfn
string_takeout_strbuf {n:nat} (str: !string n >> stringptrout(n, l))
  :<> #[m:int;l:addr | m > n] (strbuf_v (m, n, l) | ptr l)
// end of [string_takeout]

praxi
string_restore_strbuf
{m,n:int}{l:addr}
(p_sbf: strbuf_v (m, n, l), str: !stringptrout(n, l) >> string n): void
// end of [string_restore]

#symload takeout with string_takeout_strbuf
#symload restore with string_restore_strbuf

prfun strbuf_v_unsplit
  {n1:nat}
  {m2,n2:nat}
  {l:addr} (
  pf_buf: c1hars n1 @ l, pf_str: strbuf_v (m2, n2, l+n1*sizeof(char))
) : strbuf_v (n1+m2, n1+n2, l)
// end of [strbuf_v_unsplit]

fun
{} (*tmp*)
strbuf_of_bytes
  {l:addr;m:int | m > 0} (
  pf: b0ytes_v (l, m)
| p: ptr l
) :<> (strbuf_v (m, 0, l) | void)
// end of [strbuf_of_bytes]

fun
{}(*tmp*)
strbuf_of_substring
  {bsz:int} {n:int}
  {st,ln:nat | st+ln <= n; ln < bsz}
  {l:addr} (
  pf: !b0ytes bsz @ l >> strbuf (bsz, ln) @ l
| p: ptr l, str: string n, st: size st, ln: size ln
) : void

fun
{}(*tmp*)
strbuf_of_string
  {bsz:int} {n:int | n < bsz} {l:addr} (
  pf: !b0ytes bsz @ l >> strbuf (bsz, n) @ l
| p: ptr l, str: string n, n: size n
) : void

fun
{}(*tmp*)
strbuf_get_char_at
  {m,n:int}
  {i:nat | i < n} (
  sbf: &strbuf (m, n), i: size i
) :<> c1har

fun
{}(*tmp*)
strbuf_set_char_at
  {m,n:int}
  {i:nat | i < n} (
  sbf: &strbuf (m, n), i: size i, c: c1har
) :<> void

praxi
bytes_of_strbuf {bsz,n:int}
  {l:addr} (pf: strbuf_v (bsz, n, l)):<prf> bytes_v (l, bsz)

fun{}
strbuf_test_char_at_size
  {m,n:int}
  {i:nat | i <= n} (
  sbf: &strbuf (m, n), i: size i
) :<> [
  c:uint | (c > 0 && i < n) || (c == 0 && i == n)
] char c
// end of [strbuf_test_char_at]

#symload .test_at with strbuf_test_char_at_size

(* ****** ****** *)

absview
strchr_v (int, int, int, addr,addr)

praxi strchr_v_unnone :
  {c,m,n:int;l:addr}
  (strchr_v(c,m,n,l,null)) -<> strbuf_v(m,n,l)

praxi strchr_v_unsome :
  {c,m,n:int;l:addr} {l1:agz} (
    strchr_v (c,m,n,l,l1)
  ) -<> [i:nat | l1 == l+i*sizeof(char)] (
    c1hars i @ l
  , char c @ l+i*sizeof(char)
  , strbufopt_v (m-(i+1),n-(i+1),l+(i+1)*sizeof(char), c)
  )

fun
strbuf_strchr {m,n,c:int}{l:addr} (
  strbuf_v (m, n, l)
| ptr l, char c
): [l1:addr] (
  strchr_v (c, m, n, l, l1)
| ptr l1
) = "mac#strchr"

(* ****** ****** *)

fun{}
string_test_at
  {n:int}
  {i:nat | i <= n} (
  s: string (n), i: size i
) :<> [
  c:uint | (c > 0 && i < n) || (c == 0 && i == n)
] char c

fun{}
string_tail
  {n:int | n > 0} (
  s: string(n)
) :<> string(n-1)

fun{}
stropt_get {n:int} (stropt(n), &ptr? >> opt (string(n), b)): #[b:bool] bool b
