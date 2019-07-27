#include "share/HATS/temptory_staload_bucs320.hats"

#staload
_ = "./../DATS/pointer.dats"
#staload "./../SATS/slist.sats"
#staload _ = "./../DATS/slist.dats"

extern
castfn
ref_make_viewptr
  {a:vtflt}{l:addr}
  (pf: a @ l | p: ptr(l)):<> ref(a)
// end of [ref_make_viewptr]

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

implement
main0 () = print_cvars ()