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

impltmp{nv}
slist_all$pred {l} (x) = false

impltmp{nv}
slist_all {n} (sl) = let
//
fun
aux {n:int}{l:addr} (pf: !slist_v (nv, n, l) | p: ptr l): bool =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  val res = slist_all$pred<nv> (!p)
in
  if res then let
    val p_nxt = slist_node_get_next<nv> (pf_v | p)  
    val res = aux (pf_nxt | p_nxt)
    prval () = pf := slseg_v_cons (pf_v, pf_nxt)
  in
    res
  end else let
    prval () = pf := slseg_v_cons (pf_v, pf_nxt)
  in
    false
  end
end else true
//
in
  aux (sl.0 | sl.1)
end

impltmp{nv}
slist_insert_before$pred {l} (x) = false

impltmp{nv}
slist_insert_before {n} (pf_v | sl, p) = {
//
fun
aux {n:int}{l0,l1,lv,ln:addr} (
  pf_v: nv (ln) @ lv
, pf_hd: nv (l1) @ l0
, pf_lst: slist_v (nv, n, l1)
| pv: ptr lv
, p0: ptr l0
, p1: ptr l1
): (slist_v (nv, n+2, l0) | ptr l0) = let
  prval () = lemma_at_view (pf_hd)
  prval () = lemma_at_view (pf_v) 
in
  if ptr1_isneqz (p1) then let
    prval slseg_v_cons (pf_nhd, pf_nlst) = pf_lst
  in
    if slist_insert_before$pred<nv> (!p1) then let
      val () = slist_node_set_next<nv> (pf_hd | p0, pv)
      val () = slist_node_set_next<nv> (pf_v | pv, p1)
      prval pf_lst = slseg_v_cons (pf_nhd, pf_nlst)
      prval pf_res = slseg_v_cons (pf_hd, slseg_v_cons (pf_v, pf_lst))
    in
      (pf_res | p0)
    end else let
      val p2 = slist_node_get_next<nv> (pf_nhd | p1)
      val (pf_lst | p_lst) = aux (pf_v, pf_nhd, pf_nlst | pv, p1, p2)
      prval pf_lst = slseg_v_cons (pf_hd, pf_lst)
    in
      (pf_lst | p0)
    end
  end else let
    // insert after the current tail, since there is no element found
    prval slseg_v_nil () = pf_lst
    val () = slist_node_set_next<nv> (pf_hd | p0, pv)
    val () = slist_node_set_next<nv> (pf_v | pv, the_null_ptr)
    prval pf_res = slseg_v_cons (pf_hd, slseg_v_cons (pf_v, slseg_v_nil ()))
  in
    (pf_res | p0)
  end
end
//
prval pf_sl = sl.0
val p_sl = sl.1
val new_sl =
  (if ptr1_isneqz (p_sl) then let
    prval slseg_v_cons (pf_hd, pf1_sl) = pf_sl
    prval () = lemma_at_view (pf_v) 
  in
    if slist_insert_before$pred<nv> (!p_sl) then let
      val () = slist_node_set_next<nv> (pf_v | p, p_sl)
      prval pf_sl = slseg_v_cons (pf_hd, pf1_sl)
      prval pf_list = slseg_v_cons (pf_v, pf_sl)
    in
      (pf_list | p)
    end else let
      val p_next = slist_node_get_next<nv> (pf_hd | p_sl)
    in
      aux (pf_v, pf_hd, pf1_sl | p, p_sl, p_next)
    end
  end else let
    prval slseg_v_nil () = pf_sl
    val () = slist_node_set_next<nv> (pf_v | p, the_null_ptr)
    prval () = lemma_at_view (pf_v)    
    prval pf = slseg_v_cons (pf_v, slseg_v_nil ())
  in
    (pf | p)
  end) : slist (nv, n+1)
prval () = sl.0 := new_sl.0
val () = sl.1 := new_sl.1
//
}
