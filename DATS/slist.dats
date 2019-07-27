#staload "./../SATS/slist.sats"
#staload "./../SATS/pointer.sats"
#staload
_ = "./../DATS/pointer.dats"

absimpl slist(nv:node_t, n:int) = [l:addr] (slist_v (nv, n, l) | ptr l)

impltmp{nv}
slist_nil () = (slseg_v_nil{nv} () | the_null_ptr)

impltmp{nv}
slist_cons {l1,l2}{n} (pf_v | sl, p) = let
  val () = slist_node_set_next<nv> (pf_v | p, sl.1)
  val () = sl.1 := p
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
