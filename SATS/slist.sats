(** lang=markdown

Singly-linked intrusive list.
*)

viewdef
vtakeout
( v1: view
, v2: view ) = (v2, v2 -<lin,prf> v1)
viewdef
vtakeout0 (v:view) = vtakeout(void, v)

(* ****** ****** *)

absview slnode_v (vtflt, addr, addr)

prfun
lemma_at_view {a:vtflt}{l1,l2:addr} (!slnode_v (a, l1, l2)): [l1 > null] void

prfun
slnode_v_takeout
  {a:vtflt} {l1,l2:addr}
  (slnode_v (a, l1, l2))
  : (a @ l1, a @ l1 -<lin,prf> slnode_v (a, l1, l2))
prfun
slnode_v_intr
  {a:vtflt} {l:addr}
  (a @ l): [l2:addr] slnode_v (a, l, l2)

dataview
opt_vtakeout (v1:view, v2:vtflt, l:addr) =
  | {l:agz} vtakeout_some_v (v1, v2, l) of (
      v2 @ l
    , v2 @ l -<lin,prf> v1
    )
  | vtakeout_none_v (v1, v2, null)
viewdef
opt_vtakeout0 (v:vtflt, l:addr) = opt_vtakeout(void, v, l)

dataview slseg_v (
  a: vtflt
, int
, addr
, addr
) =
  | {n:nat}
    {la,lb,lz:addr | la > null}
    slseg_v_cons (a, n+1, la, lz) of (
      slnode_v (a, la, lb), slseg_v (a, n, lb, lz)
    ) // end of [slseg_v_cons]
  | {la:addr} slseg_v_nil (a, 0, la, la)

viewdef slist_v
  (a: vtflt, n:int, l:addr) = slseg_v (a, n, l, null)

prfun
lemma_slseg_v_param {a:vtflt;n:int;l1,l2:addr} (
  !slseg_v(a, n, l1, l2)
):<> [n>=0] void

fun{a:vtflt}
slist_node_get_next {l1,l2:addr} (
  v: !slnode_v(a, l1, l2) | ptr l1
): ptr l2

fun{a:vtflt}
slist_node_set_next {l1,l2,l3:addr} (
  v: !slnode_v(a, l1, l2) >> slnode_v(a, l1, l3) | ptr l1, ptr l3
): void

absvtbox slist(vtflt+, int) = ptr
vtypedef slist0 (a:vtflt) = [n:int] slist(a, n)

fun{a:vtflt}
slist_nil (): slist (a, 0)

fun{a:vtflt}
slist_cons {l:addr}{n:int} (
  v: a @ l | &slist(a, n) >> slist(a, n+1), ptr l
): void

fun{a:vtflt}
slist_foreach {n:int} (
  &slist (a, n)
): void

fun{a:vtflt}
slist_foreach$work (&a): void

fun{a:vtflt}
slist_iforeach {n:int} (
  &slist (a, n)
): void

fun{a:vtflt}
slist_iforeach$work (int, &a): void

fun{a:vtflt}
slist_search$pred (&a): bool

fun{a:vtflt}
slist_search_takeout {n:int} (!slist (a, n)): [l:addr] (
  opt_vtakeout0 (a, l)
| ptr l
)

// evaluate predicate over all nodes
fun{a:vtflt}
slist_all$pred (x: &a): bool
fun{a:vtflt}
slist_all {n:int} (!slist (a, n)): bool

fun{a:vtflt}
slist_insert_before$pred (x : &a): bool

// insert node into list before the first node
// where [slist_insert_before$pred] evaluates to [true],
// or at the very end of list (if no such node exists)
fun{a:vtflt}
slist_insert_before {n:int}{l:addr} (
  v: a @ l
| &slist (a, n) >> slist (a, n+1)
, ptr l
): void
