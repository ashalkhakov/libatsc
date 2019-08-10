#include "share/HATS/temptory_staload_bucs320.hats"

#staload "./../SATS/pointer.sats"
#staload
_ = "./../DATS/pointer.dats"

#staload "./../SATS/slist.sats"
#staload _ = "./../DATS/slist.dats"

(* ****** ****** *)

typedef node (l:addr) = @{name= string, help= string, next= ptr l}
typedef node0 = node(null)
typedef nv (l1:addr) = node (l1)
typedef nv = [l:addr] nv (l)

extern
prfun
slnode_v_get {l1,l2:addr} (slnode_v(nv, l1, l2)): nv (l2) @ l1
extern
prfun
slnode_v_put {l1,l2:addr} (nv(l2) @ l1): slnode_v (nv, l1, l2)

impltmp
slist_node_get_next<nv> {l1,l2} (pf_v | p) = let
  prval pf_at = slnode_v_get (pf_v)
  val res = !p.next
  prval () = pf_v := slnode_v_put (pf_at)
in
  res
end
impltmp
slist_node_set_next<nv> {l1,l2,l3} (pf_v | p, n) = {
  prval pf_at = slnode_v_get (pf_v)
  val () = !p.next := n
  prval () = pf_v := slnode_v_put (pf_at)
}

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
  prval pf_v = slnode_v_put pf_at
  val () = $effmask_all (slist_cons<nv> (pf_v | !p_cvarlist, p))
in
end

fun
lookup_print (name: string): void = let
  val (vbox pf_cvarlist | p_cvarlist) = ref_vptrof {cvarlist} (the_cvars)
  val (pf_opt | p_opt) = $effmask_ref (slist_search_takeout<nv>(!p_cvarlist))
  where {
    impltmp
    slist_search$pred<nv> (x) = (x.name = name)
  }
in
  if ptr1_isneqz p_opt then {
    prval vtakeout_some_v (pf_at, fpf) = pf_opt
    val () = $effmask_ref (
      println!("found ", name, ", the help text is: ", !p_opt.help)
    )
    prval () = fpf (pf_at)
  } else {
    val () = $effmask_ref (
      println!("sorry, the variable named ", name, " is not found")
    )
    prval vtakeout_none_v () = pf_opt
  }
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
main0 () = {
val () = print_cvars ()
val () = lookup_print ("input")
val () = lookup_print ("help")
val () = lookup_print ("anything")
}
