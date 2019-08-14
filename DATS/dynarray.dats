(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2019 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
**
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
**
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi, Artyom Shalkhakov *)
(* Start time: June, 2019 *)
(* Authoremail: hwxiATcsDOTbuDOTedu, artyomDOTshalkhakovATgmailDOTcom *)

(* ****** ****** *)

#staload "libats/SATS/gint.sats"
#staload "libats/SATS/gptr.sats"
#staload "libats/SATS/array.sats"
#staload "libats/basics_gen.sats"

#staload "./../SATS/array_prf.sats"

#staload "./../SATS/pointer.sats"

#staload "./../SATS/dynarray.sats"
#staload LIBC_STRING = "./../SATS/libc_string.sats"

#staload UN = "libats/SATS/unsafe.sats"

(* ****** ****** *)

extern
prfun
lemma_size_param {i:int} (size(i)): [i>=0] void

(* ****** ****** *)

impltmp
{a} (*tmp*)
dynarray$frealloc {l,m,n,m1} (
  pf0_arr, pf1_arr, pf_gc
| p, m, n, m1
) = let
  val (pfz_arr, pfz_gc | pz) = array_ptr_alloc<a>(m1)

  prval (pfz1_arr, pfz2_arr) = array_v_split_at (pfz_arr | n)

  val nb = n*sizeof<a>
  val (pf0_arr1, pfz1_arr | _) =
    $LIBC_STRING.memcpy (pf0_arr, pfz1_arr | pz, p, nb)

  prval pf_arr = array_v_unsplit {a?} (pf0_arr1, pf1_arr)
  val () = $effmask_all (array_ptr_mfree<> (pf_arr, pf_gc | p))
in
  (pfz1_arr, pfz2_arr, pfz_gc | pz)
end

(* ****** ****** *)

local

dataprop myprop (int, int) = {m,n:int | m > 0; n >= 0; n <= m} MYPROP (m, n)

vtypedef
DYNARRAY (a:vtflt, m:int, n:int, l:addr) = (
  array_v(a, l, n)
, array_v(a?, l+n*sizeof(a), m-n)
, mfree_gc_v (l)
, myprop (m, n)
| DYNARRAYNODE (m, n, l)
)

extern
prfun
dynarray_pack {a:vtflt}{m,n:int}{l:addr} (
  array_v(a, l, n)
, array_v(a?, l+n*sizeof(a), m-n)
, mfree_gc_v (l)
, myprop (m, n)
| !DYNARRAYNODE(m, n, l) >> DYNARRAY (a, m, n, l)
): void

extern
prfun
dynarray_unpack {a:vtflt}{m,n:int}{l:addr} (
 !DYNARRAY (a, m, n, l) >> DYNARRAYNODE(m, n, l)
): (
  array_v(a, l, n)
, array_v(a?, l+n*sizeof(a), m-n)
, mfree_gc_v (l)
, myprop (m, n)
| void
)


vtypedef
dynarray(a:vtflt, m: int, n:int) = [l:addr] DYNARRAY (a, m, n, l)

absimpl
dynarray_vtflt_int_tflt(a, n) = [m:int;l:addr] DYNARRAY (a, m, n, l)

in (* in-of-local *)

impltmp
{a}(*tmp*)
dynarray_make_nil
  (A, m) = {
//
val (pf1_arr, pf_gc | p) = array_ptr_alloc<a>(m)
val () = A.data := p
val () = A.len := (i2sz)0
val () = A.cap := m
//
prval () = dynarray_pack (array_v_nil{a}(), pf1_arr, pf_gc, MYPROP() | A)
//
}

impltmp
{}(*tmp*)
dynarray_free_tflt {a}{n}
  (DA) = {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval() = lemma_array_v_param(pf0_arr)
//
prval pf_arr = array_v_unsplit {a?} (pf0_arr, pf1_arr)
val () = $effmask_all (array_ptr_mfree<> (pf_arr, pf_gc | p))
//
} (* end of [dynarray_free_tflt] *)

impltmp
{a}(*tmp*)
dynarray_free {n}
  (DA) = {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval() = lemma_array_v_param(pf0_arr)
//
fun
loop
{l:addr}{n:nat} .<n>. (
  pf: array_v (a, l, n)
| p0: ptr(l), nz: size(n)
): (array_v (a?, l, n) | void) =
if nz > i2sz(0) then let
  prval (pf_at, pf) = array_v_uncons{a} (pf)
  val () = gfree$ref<a>(!p0)
  val (pf | ()) = loop (pf | ptr1_succ(p0), pred(nz))
  prval pf_res = array_v_cons{a?} (pf_at, pf)
in
  (pf_res | ((*empty*)))
end else let
  prval () = array_v_unnil{a} (pf)
  prval pf_res = array_v_nil{a?} ()
in
  (pf_res | ((*empty*)))
end
//
val (pf0_arr | ()) = $effmask_all (loop (pf0_arr | p, n))
//
prval pf_arr = array_v_unsplit {a?} (pf0_arr, pf1_arr)
val () = $effmask_all (array_ptr_mfree<> (pf_arr, pf_gc | p))
//
} (* end of [dynarray_free] *)

impltmp{}
dynarray_get_size{a}{n}(DA) =
n where
{
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val n = DA.len
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
}

impltmp{}
dynarray_get_capacity{a}{n}(DA) =
m where
{
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val m = DA.cap
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
}

impltmp{}
dynarray_takeout_array {a}{n}(DA) = let
  prval (pf0_arr, pf1_arr, pf_gc, MYPROP () | ()) = dynarray_unpack (DA)
  val p = DA.data
  val cap = DA.cap
  val len = DA.len
  prval () = __trustme(DA, pf_gc | p) where {
    extern
    prfun
    __trustme {m:int}{l:addr} (
      !DYNARRAYNODE(m, n, l) >> dynarrayptrout(a,l,n)
    , mfree_gc_v (l)
    | ptr l
    ) : void
  }
in
  (pf0_arr, pf1_arr | p, cap, len)
end

impltmp{}
dynarray_restore_array
{a}{l}{m,n,n1}(pf0_arr, pf1_arr | DA, cap, len) = let
  prval pf_gc = __trustme(DA) where {
    extern
    prfun
    __trustme (
      !dynarrayptrout(a, l, n) >> DYNARRAYNODE(m, n, l)
    ) : mfree_gc_v (l)
  }
  prval () = __positive_cap () where {
    extern
    prfun
    __positive_cap (): [m > 0] void
  }
  prval () = lemma_size_param (len)
  val () = DA.len := len
  prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP () | DA)
in
end

impltmp{}
dynarray_takeout{a}{n}(DA) =
(arr, n) where
{
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val n = DA.len
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
val arr = __trustme(DA | p)
where {
  extern
  castfn
  __trustme {m:int}{l:addr} (
    !DYNARRAY (a, m, n, l) >> dynarrayptrout(a,l,n)
  | ptr l
  ) : arrayptr(a,l,n)
}
}

impltmp
{a}
dynarray_get_at_sint {n}{i}
  (DA, i) = res where {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val res = array_get_at_sint<a> (!(DA.data), i)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a}
dynarray_set_at_sint {n}{i}
  (DA, i, x) = {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val () = array_set_at_sint<a> (!(DA.data), i, x)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a}
dynarray_get_at_size {n}{i}
  (DA, i) = res where {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val res = array_get_at_size<a> (!(DA.data), i)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a}
dynarray_set_at_size {n}{i}
  (DA, i, x) = {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val () = array_set_at_size<a> (!(DA.data), i, x)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a}
dynarray_getref_at_sint {n}{i}
  (DA, i) = res where {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val res = array_getref_at_sint<a> (!(DA.data), i)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a}
dynarray_getref_at_size {n}{i}
  (DA, i) = res where {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val res = array_getref_at_size<a> (!(DA.data), i)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

// insertions

impltmp{}
dynarray$fgrow {n,d} (cap, delta) = res where {
  // TODO: use a factor of 1.5 or 1.45
  val res = cap + cap
}

extern
fun{a:vtflt}
recapacitize {n,m,m1:uint} (
  &dynarray(a, m, n) >> dynarray (a, max(m,m1), n), m1: size(m1)
): void

impltmp
{a} (*tmp*)
recapacitize {n,m,m1}
  (DA, m1) = let
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val m = DA.cap
val n = DA.len
val p = DA.data
//
in
//
if m1 <= m then let
  prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
in
end else let
  val (
    pfz1_arr, pfz2_arr, pfz_gc | pz
  ) = dynarray$frealloc<a>(pf0_arr, pf1_arr, pf_gc | p, m, n, m1)
  prval () = pf0_arr := pfz1_arr
  prval () = pf1_arr := pfz2_arr
  prval () = pf_gc := pfz_gc
  val () = DA.data := pz
  val () = DA.cap := m1
  prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
in
end
//
end

impltmp
{a} (*tmp*)
dynarray_insert_at{n}{i}
  (DA, i, x) = let
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
val m1 = dynarray$fgrow<> (m, i2sz 1)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
val () = recapacitize<a> (DA, m1)
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval (pf01_arr, pf02_arr) = array_v_split_at (pf0_arr | i)
prval (pf_kat, pf10_arr) = array_v_uncons {a?} (pf1_arr)
prval pf_karr = array_v_cons {a?} (pf_kat, array_v_nil{a?} ())
val src = ptr1_add<a> (p, i)
val dst = ptr1_add<a> (p, succ(i))
val nb = (g1sub_usize1_usize1(n, i))*sizeof<a> where {
//
extern
fun
g1sub_usize1_usize1
{i,j:int
|i >= j}
( x
: usize(i)
, y
: usize(j)):<> usize(i-j) = "mac#temptory_g1sub_usize1_usize1"
//
}
val (pf_karr, pf02_arr | _) =
  $LIBC_STRING.memmove_right (pf02_arr, pf_karr | dst, src, nb)
prval (pf_kat, pf_karr) = array_v_uncons{a?} (pf_karr)
prval () = array_v_unnil {a?} (pf_karr)
//
var x = x
val () = ptr_write<a> (pf_kat | src, x)
//
prval pf02_arr = array_v_cons {a} (pf_kat, pf02_arr)
prval () = pf0_arr := array_v_unsplit {a} (pf01_arr, pf02_arr)
prval () = pf1_arr := pf10_arr
val () = DA.len := succ(n)
//
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
in
end

impltmp
{a} (*tmp*)
dynarray_append{n}
  (DA, x) = let
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
val m1 = dynarray$fgrow<> (m, i2sz 1)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
val () = recapacitize<a> (DA, m1)
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval (pf1_at, pf11_arr) = array_v_uncons{a?}(pf1_arr)
val dst = ptr1_add<a> (p, n)
var x = x
val () = ptr_write<a> (pf1_at | dst, x)
prval pf01_arr = array_v_extend (pf0_arr, pf1_at)
prval () = pf0_arr := pf01_arr
prval () = pf1_arr := pf11_arr
val () = DA.len := succ(n)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
in
end

// deletions

impltmp
{a} (*tmp*)
dynarray_takeout_at{n,i}
  (DA, i, res) = let
//
val sz = dynarray_get_size(DA)
//
in
//
if succ(i) = sz then dynarray_takeout_last (DA, res)
else
{
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval (pf01_arr, pf02_arr) = array_v_split_at (pf0_arr | i)
prval (pf_kat, pf02_arr) = array_v_uncons {a} (pf02_arr)
val dst = ptr1_add<a> (p, i)
val src = ptr1_add<a> (p, succ(i))
//
val () = res := ptr_read<a> (pf_kat | dst)
//
prval pf_karr = array_v_cons {a?} (pf_kat, array_v_nil{a?} ())
//
val nb = (n-succ(i))*sizeof<a>
val (pf02_arr, pf_karr | _) =
  $LIBC_STRING.memmove_left{a} (pf_karr, pf02_arr | dst, src, nb)
prval () = pf0_arr := array_v_unsplit (pf01_arr, pf02_arr)
//
prval pf11_arr = array_v_unsplit (pf_karr, pf1_arr)
//
prval () = pf1_arr := pf11_arr
val () = DA.len := pred(n)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}
end

impltmp
{a} (*tmp*)
dynarray_takeout_last{n}
  (DA, res) = {
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
//
prval (pf01_arr, pf1_at) = array_v_unextend{a}(pf0_arr)
val src = ptr1_add<a> (p, pred(n))
val () = res := !src
prval pf11_arr = array_v_cons {a?} (pf1_at, pf1_arr)
prval () = pf0_arr := pf01_arr
prval () = pf1_arr := pf11_arr
val () = DA.len := pred(n)
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
}

impltmp
{a} (*tmp*)
dynarray_reset_capacity {n}
  (DA, m1) = let
//
prval (pf0_arr, pf1_arr, pf_gc, MYPROP() | ()) = dynarray_unpack (DA)
val p = DA.data
val m = DA.cap
val n = DA.len
val cap = m
prval () = dynarray_pack (pf0_arr, pf1_arr, pf_gc, MYPROP() | DA)
//
in
  if :(DA: dynarray(a, n)) => m1 <= cap then false
  else let
    val () = $effmask_all (recapacitize<a> (DA, m1))
  in
    true
  end
end

end (* end-of-local *)

(* ****** ****** *)

(* end of [dynarray.dats] *)
