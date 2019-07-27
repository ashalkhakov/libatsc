#include "share/HATS/temptory_staload_bucs320.hats"

#staload "./../SATS/array_prf.sats"
#staload LIBC_STRING = "./../SATS/libc_string.sats"

#staload "./../SATS/pointer.sats"
#staload _ = "./../DATS/pointer.dats"

dataprop
EQADDR(addr, addr) = {x:addr} EQADDR(x, x)
extern
prfun
eqaddr_make{x,y:addr | x == y}(): EQADDR(x, y)
extern
prfun
eqaddr_make_ptr{x:addr}(x: ptr(x)): [y:addr] EQADDR(x, y)

//
extern
praxi
lemma_size_param
  {n:int} (x: size(n)): [n >= 0] void
//

extern
castfn
ref_make_viewptr
  {a:vtflt}{l:addr}
  (pf: a @ l | p: ptr(l)):<> ref(a)
// end of [ref_make_viewptr]

sortdef free_v = (addr) -> view

typedef
free_type (fv:free_v, a:vtflt, l:addr, n:int) =
  (array_v (a?, l, n), fv(l) | ptr(l)) -> void
typedef
alloc_type (fv:free_v, a:vtflt, n:int) =
  (size(n)) -> [l:agz] (array_v(a?,l,n), fv(l) | ptr(l))  

extern
fun{fv:free_v}
free
{a:vtflt}{l:addr}{n:int} : free_type (fv, a, l, n)

extern
fun
{fv:free_v}{a:vtflt}
alloc
  {n:int} : alloc_type (fv, a, n)

extern
fun{fv:free_v}
free_single
{a:vtflt}{l:addr}{n:int}
(a? @ l, fv(l) | ptr(l)): void
extern
fun
{fv:free_v}{a:vtflt}
alloc_single {n:int}
(): [l:agz] (a? @ l, fv(l) | ptr(l))

extern
fun{fv:free_v}{a:vtflt}
realloc
  {l:addr;m,n,m1:int | m > 0; n >= 0; n <= m; m < m1} (
  array_v(a, l, n), array_v(a?, l+n*sizeof(a), m-n), fv(l)
| ptr l, size m, size n, size m1
): [l1:addr] (
  array_v(a, l1, n), array_v(a?, l1+n*sizeof(a), m1-n), fv(l1)
| ptr l1
)

(* ****** ****** *)

impltmp{fv}
free_single
{a}{l}{n}
(pf_at, pf_gc | p) = {
//
prval pf_arr = array_v_cons {a?} (pf_at, array_v_nil {a?} ())
val () = free<fv> (pf_arr, pf_gc | p)
//
}

impltmp{fv}{a}
alloc_single {n} () =
(pf_at, pf_gc | p)
where {
//
val (pf_arr, pf_gc | p) = alloc<fv><a> (i2sz 1)
prval (pf_at, pf1_arr) = array_v_uncons (pf_arr)
prval () = array_v_unnil (pf1_arr)
//
}

impltmp{fv}{a}
realloc {l,m,n,m1} (pf0_arr, pf1_arr, pf_gc | p, m, n, m1) = let
  val (pfz_arr, pfz_gc | pz) = alloc<fv><a>(m1)

  prval (pfz1_arr, pfz2_arr) = array_v_split_at (pfz_arr | n)

  val nb = n*sizeof<a>
  val (pf0_arr1, pfz1_arr | _) =
    $LIBC_STRING.memcpy (pf0_arr, pfz1_arr | pz, p, nb)

  prval pf_arr = array_v_unsplit {a?} (pf0_arr1, pf1_arr)
  val () = $effmask_all (free<fv> (pf_arr, pf_gc | p))
in
  (pfz1_arr, pfz2_arr, pfz_gc | pz)
end

(* ****** ****** *)

// base allocator

impltmp
free<mfree_gc_v> {a}{l}{n} (pf_arr, pf_gc | p) =
  array_ptr_mfree (pf_arr, pf_gc | p)

impltmp(a)
alloc<mfree_gc_v><a> {n} (asz) =
  array_ptr_alloc (asz)

(* ****** ****** *)



(* ****** ****** *)

implement
main0 () = let
  // usage:
  val (pf_arr, pf_gc | p) = alloc<mfree_gc_v><int>(i2sz 32)
  val () = free<mfree_gc_v>(pf_arr, pf_gc | p)
in
(println!("hello"))
end
