// NOTE: based on this code: https://gist.github.com/martinkunev/1365481

#staload
DA = "./dynarray.sats"

sexpdef HEAPNODE = $DA.DYNARRAYNODE

fun{T:vtflt}
gcompare$ptr {l1,l2:addr} (!T @ l1, !T @ l2 | ptr l1, ptr l2): int

(* ****** ****** *)
//
typedef
HEAPNODE0 = HEAPNODE (0, 0, null)
//
absvtflt
heap_vtflt_int_tflt (a:vtflt+,n:int) = HEAPNODE (0, 0, null)
//
sexpdef
heap = heap_vtflt_int_tflt
//

(* ****** ****** *)

fun{a:tflt}
heap_make_nil (
  H: &HEAPNODE0? >> heap (a, 0)
, cap: Sizegt(0)
): void

fun{a:tflt}
heap_free_tflt {n:int} (
  H: &heap (INV(a), n) >> HEAPNODE0?
): void

fun{a:vtflt}
heap_free {n:int} (
  H: &heap (INV(a), n) >> HEAPNODE0?
): void

(* ****** ****** *)

fun
{a:tflt}
heap_front {n:pos}
(H: &heap (INV(a),  n)): a

fun
{a:vtflt}
heap_getref_front {n:pos}
(H: &heap (INV(a), n)): cptr(a)

fun{}
heap_get_size {a:vtflt} {n:int}
(H: &heap (a, n)): size(n)

fun{}
heap_get_capacity {a:vtflt} {n:int} (
  H: &heap (a, n)
): [m:int | m >= n] size(m)

(* ****** ****** *)

fun{a:vtflt}
heap_push {n:int} (
  &heap (a, n) >> heap (a, n+1), INV(a)
): void

fun{a:vtflt}
heap_pop {n:pos} (
  &heap (INV(a), n) >> heap (a, n-1)
): a

(* ****** ****** *)

fun{a:tflt}
heap_reset_capacity {n:int} (
  &heap (INV(a), n) >> _, Sizegte(1)
):<!wrt> bool(*done/ignored*)
