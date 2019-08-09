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

sortdef node_t = addr -> tflt

dataview
opt_vtakeout (v1:view, v2:node_t, l:addr) =
  | {ln:addr;l:agz} vtakeout_some_v (v1, v2, l) of (
      v2(ln) @ l
    , v2(ln) @ l -<lin,prf> v1
    )
  | vtakeout_none_v (v1, v2, null)
viewdef
opt_vtakeout0 (v:node_t, l:addr) = opt_vtakeout(void, v, l)

prfun
lemma_at_view {nv:node_t}{l1,l2:addr} (!nv (l2) @ l1): [l1 > null] void

dataview slseg_v (
  a: node_t
, int
, addr
, addr
) =
  | {n:nat}
    {la,lb,lz:addr | la > null}
    slseg_v_cons (a, n+1, la, lz) of (
      a (lb) @ la, slseg_v (a, n, lb, lz)
    ) // end of [slseg_v_cons]
  | {la:addr} slseg_v_nil (a, 0, la, la)

viewdef slist_v
  (a: node_t, n:int, l:addr) = slseg_v (a, n, l, null)

prfun
lemma_slseg_v_param {nv:node_t;n:int;l1,l2:addr} (
  !slseg_v(nv, n, l1, l2)
):<> [n>=0] void

fun{nv:node_t}
slist_node_get_next {l1,l2:addr} (
  v: !nv(l2) @ l1 | ptr l1
): ptr l2

fun{nv:node_t}
slist_node_set_next {l1,l2,l3:addr} (
  v: !nv(l2) @ l1 >> nv(l3) @ l1 | ptr l1, ptr l3
): void

absvtbox slist(node_t, int) = ptr
vtypedef slist0 (a:node_t) = [n:int] slist(a, n)

fun{nv:node_t}
slist_nil (): slist (nv, 0)

fun{nv:node_t}
slist_cons {l1,l2:addr}{n:int} (
  v: nv(l2) @ l1 | &slist(nv, n) >> slist(nv, n+1), ptr l1
): void

fun{nv:node_t}
slist_foreach {n:int} (
  &slist (nv, n)
): void

fun{nv:node_t}
slist_foreach$work {l:addr} (x : &nv(l)): void

fun{nv:node_t}
slist_iforeach {n:int} (
  &slist (nv, n)
): void

fun{nv:node_t}
slist_iforeach$work {l:addr} (int, x : &nv(l)): void

fun{nv:node_t}
slist_search$pred {l:addr} (x : &nv(l)): bool

fun{nv:node_t}
slist_search_takeout {n:int} (!slist (nv, n)): [l1:addr] (
  opt_vtakeout0 (nv, l1)
| ptr l1
)

// evaluate predicate over all nodes
fun{nv:node_t}
slist_all$pred {l:addr} (x: &nv(l)): bool
fun{nv:node_t}
slist_all {n:int} (!slist (nv, n)): bool

fun{nv:node_t}
slist_insert_before$pred {l:addr} (x : &nv(l)): bool

// insert node into list before the first node
// where [slist_insert_before$pred] evaluates to [true],
// or at the very end of list (if no such node exists)
fun{nv:node_t}
slist_insert_before {n:int}{l1,l2:addr} (
  v: nv(l2) @ l1
| &slist (nv, n) >> slist (nv, n+1)
, ptr l1
): void
