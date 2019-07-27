#include "share/HATS/temptory_staload_bucs320.hats"

extern
castfn
ref_make_viewptr
  {a:vtflt}{l:addr}
  (pf: a @ l | p: ptr(l)):<> ref(a)
// end of [ref_make_viewptr]

extern
fun{}
ptr1_isneqz
{l:addr}(ptr(l)):<> bool(l>null)
impltmp
{}//tmp
ptr1_isneqz{l}(p0) =
$UN.cast{bool(l>null)}(ptr0_isneqz(p0))

(* ****** ****** *)

sortdef node_t = addr -> tflt

extern
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

extern
prfun
lemma_slseg_v_param {nv:node_t;n:int;l1,l2:addr} (
  !slseg_v(nv, n, l1, l2)
):<> [n>=0] void

extern
fun{nv:node_t}
slist_node_get_next {l1,l2:addr} (
  v: !nv(l2) @ l1 | ptr l1
): ptr l2

extern
fun{nv:node_t}
slist_node_set_next {l1,l2,l3:addr} (
  v: !nv(l2) @ l1 >> nv(l3) @ l1 | ptr l1, ptr l3
): void

absvtbox slist(node_t, int) = ptr
vtypedef slist0 (a:node_t) = [n:int] slist(a, n)

extern
fun{nv:node_t}
slist_nil (): slist (nv, 0)

extern
fun{nv:node_t}
slist_cons {l1,l2:addr}{n:int} (
  v: nv(l2) @ l1 | &slist(nv, n) >> slist(nv, n+1), ptr l1
): void

extern
fun{nv:node_t}
slist_foreach {n:int} (
  &slist (nv, n)
): void
extern
fun{nv:node_t}
slist_foreach$work {l:addr} (x : &nv(l)): void

(* ****** ****** *)

local

absimpl slist(nv:node_t, n:int) = [l:addr] (slist_v (nv, n, l) | ptr l)

in

impltmp{nv}
slist_nil () = (slseg_v_nil{nv} () | the_null_ptr)

impltmp{nv}
slist_cons {l1,l2}{n} (pf_v | sl, p) = let
  val () = slist_node_set_next<nv> (pf_v | p, sl.1)
  val () = sl.1 := p
  val () = assertloc(p > the_null_ptr)
  prval () = lemma_slseg_v_param (sl.0)
  prval () = lemma_at_view (pf_v)
  prval () = sl.0 := slseg_v_cons {nv} (pf_v, sl.0)
in
end

impltmp{nv}
slist_foreach$work {l} (x) = ()

impltmp{nv}
slist_foreach {n} (sl) = aux (sl.0 | sl.1)
where
{
fun
aux {n:int}{l:addr} (pf: !slist_v (nv, n, l) | p: ptr l): void =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  val () = slist_foreach$work<nv> (!p)
  val p_nxt = slist_node_get_next<nv> (pf_v | p)  
  val () = aux (pf_nxt | p_nxt)
  prval () = pf := slseg_v_cons (pf_v, pf_nxt)
in
end else ()
}

end

(* ****** ****** *)

typedef node (l:addr) = @{name= string, help= string, next= ptr l}
typedef node0 = node(null)
typedef nv (l1:addr) = node (l1)

impltmp
slist_node_get_next<nv> {l1,l2} (pf_v | p) = !p.next
impltmp
slist_node_set_next<nv> {l1,l2,l3} (pf_v | p, n) = !p.next := n

vtypedef
cvarlist = [n:int] slist (nv, n)

var cvars = slist_nil<nv> ()
val the_cvars = ref_make_viewptr (view@ cvars | addr@ cvars)

fun
register {l:addr} (
  pf_at: node0? @ l | p: ptr l, name: string, help: string
): void = let
  val () = !p.name := name
  val () = !p.help := help
  val () = !p.next := the_null_ptr

  val (vbox pf_cvarlist | p_cvarlist) = ref_vptrof {cvarlist} (the_cvars)
  val () = $effmask_all (slist_cons<nv> (pf_at | !p_cvarlist, p))
in
end

fun
print_cvars (): void = let
  val (vbox pf_cvarlist | p_cvarlist) = ref_vptrof {cvarlist} (the_cvars)
  val () = $effmask_ref (slist_foreach<nv> (!p_cvarlist)) where
  {
  impltmp
  slist_foreach$work<nv> (x) = println!(x.name, ": ", x.help)
  }
in
end

//

var x : node0
val () = register (view@ x | addr@ x, "help", "print help")
var y : node0
val () = register (view@ y | addr@ y, "output", "specify output")
var z : node0
val () = register (view@ z | addr@ z, "input", "specify input")

fun
test(): void = {
  val () = print_cvars ()
}


implement
main0 () = (test(); println!("hello"))
