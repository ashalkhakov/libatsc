#staload "libats/SATS/gint.sats"
#staload
_ = "libats/DATS/gint.dats"

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

impltmp{nv}
slist_iforeach$work {l} (i, x) = ()

impltmp{nv}
slist_iforeach {n} (sl) = aux (sl.0 | 0, sl.1)
where
{
fun
aux {n:int}{l:addr} (pf: !slist_v (nv, n, l) | i: int, p: ptr l): void =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  val () = slist_iforeach$work<nv> (i, !p)
  val p_nxt = slist_node_get_next<nv> (pf_v | p)  
  val () = aux (pf_nxt | i+1, p_nxt)
  prval () = pf := slseg_v_cons (pf_v, pf_nxt)
in
end else ()
}


impltmp{nv}
slist_search$pred {l} (x) = false

impltmp{nv}
slist_search_takeout {n} (sl) = aux (sl.0 | sl.1)
where
{
//
fun
aux {n:int}{l:addr} (
  pf: !slist_v (nv, n, l)
| p: ptr (l)
): [lp:addr] (
  opt_vtakeout0 (nv, lp)
| ptr (lp)
) =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  val found = slist_search$pred<nv> (!p)
in
  if found then let
    // duplicate the at-proof
    prval (pf_at_res, fpf_at_res) = __trustme (pf_v) where {
      extern
      prfun
      __trustme {l1,l2:addr | l1 > null} (
        !nv(l2) @ l1
      ): (nv(l2) @ l1, nv(l2) @ l1 -<lin,prf> void)
    }
    prval () = pf := slseg_v_cons (pf_v, pf_nxt)
  in
    (vtakeout_some_v (pf_at_res, fpf_at_res) | p)
  end else let
    val p_nxt = slist_node_get_next<nv> (pf_v | p)
    val (pf_res | p_res) = aux (pf_nxt | p_nxt)
    prval () = pf := slseg_v_cons (pf_v, pf_nxt)
  in
    (pf_res | p_res)
  end
end else let
in
  (vtakeout_none_v () | the_null_ptr)
end
//
}
