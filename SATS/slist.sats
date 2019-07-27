sortdef node_t = addr -> tflt

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
