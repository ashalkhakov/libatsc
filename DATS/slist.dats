#staload "libats/SATS/gint.sats"
#staload
_ = "libats/DATS/gint.dats"

#staload "./../SATS/slist.sats"
#staload "./../SATS/pointer.sats"
#staload
_ = "./../DATS/pointer.dats"

absimpl slist(a:vtflt, n:int) = [l:addr] (slist_v (a, n, l) | ptr l)

impltmp{a}
slist_nil () = (slseg_v_nil{a} () | the_null_ptr)

impltmp{a}
slist_cons {l}{n} (pf_at | sl, p) = let
  prval pf_v = slnode_v_intr (pf_at)
  val () = slist_node_set_next<a> (pf_v | p, sl.1)
  val () = sl.1 := p
  prval () = lemma_slseg_v_param (sl.0)
  prval () = lemma_at_view (pf_v)
  prval () = sl.0 := slseg_v_cons {a} (pf_v, sl.0)
in
end

impltmp{a}
slist_foreach$work (x) = ()

impltmp{a}
slist_foreach {n} (sl) = aux (sl.0 | sl.1)
where
{
fun
aux {n:int}{l:addr} (pf: !slist_v (a, n, l) | p: ptr l): void =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  prval (pf_v_at, fpf_v_at) = slnode_v_takeout (pf_v)
  val () = slist_foreach$work<a> (!p)
  prval pf_v = fpf_v_at (pf_v_at)
  val p_nxt = slist_node_get_next<a> (pf_v | p)  
  val () = aux (pf_nxt | p_nxt)
  prval () = pf := slseg_v_cons (pf_v, pf_nxt)
in
end else ()
}

impltmp{a}
slist_iforeach$work (i, x) = ()

impltmp{a}
slist_iforeach {n} (sl) = aux (sl.0 | 0, sl.1)
where
{
fun
aux {n:int}{l:addr} (pf: !slist_v (a, n, l) | i: int, p: ptr l): void =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  prval (pf_v_at, fpf_v_at) = slnode_v_takeout (pf_v)
  val () = slist_iforeach$work<a> (i, !p)
  prval pf_v = fpf_v_at (pf_v_at)
  val p_nxt = slist_node_get_next<a> (pf_v | p)  
  val () = aux (pf_nxt | i+1, p_nxt)
  prval () = pf := slseg_v_cons (pf_v, pf_nxt)
in
end else ()
}

impltmp{a}
slist_search$pred (x) = false

impltmp{a}
slist_search_takeout {n} (sl) = aux (sl.0 | sl.1)
where
{
//
fun
aux {n:int}{l:addr} (
  pf: !slist_v (a, n, l)
| p: ptr (l)
): [lp:addr] (
  opt_vtakeout0 (a, lp)
| ptr (lp)
) =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  prval (pf_v_at, fpf_v_at) = slnode_v_takeout (pf_v)
  val found = slist_search$pred<a> (!p)
  prval pf_v = fpf_v_at (pf_v_at)
in
  if found then let
    // duplicate the at-proof
    prval (pf_at_res, fpf_at_res) = __trustme (pf_v) where {
      extern
      prfun
      __trustme {l1,l2:addr | l1 > null} (
        !slnode_v(a, l1, l2)
      ): (a @ l1, a @ l1 -<lin,prf> void)
    }
    prval () = pf := slseg_v_cons (pf_v, pf_nxt)
  in
    (vtakeout_some_v (pf_at_res, fpf_at_res) | p)
  end else let
    val p_nxt = slist_node_get_next<a> (pf_v | p)
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

impltmp{a}
slist_all$pred (x) = false

impltmp{a}
slist_all {n} (sl) = let
//
fun
aux {n:int}{l:addr} (pf: !slist_v (a, n, l) | p: ptr l): bool =
if ptr1_isneqz (p) then let
  prval slseg_v_cons (pf_v, pf_nxt) = pf
  prval (pf_v_at, fpf_v_at) = slnode_v_takeout (pf_v)
  val res = slist_all$pred<a> (!p)
  prval pf_v = fpf_v_at (pf_v_at)
in
  if res then let
    val p_nxt = slist_node_get_next<a> (pf_v | p)  
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

impltmp{a}
slist_insert_before$pred (x) = false

impltmp{a}
slist_insert_before {n} (pf_v | sl, p) = {
//
fun
aux {n:int}{l0,l1,lv,ln:addr} (
  pf_v: slnode_v (a, lv, ln)
, pf_hd: slnode_v (a, l0, l1)
, pf_lst: slist_v (a, n, l1)
| pv: ptr lv
, p0: ptr l0
, p1: ptr l1
): (slist_v (a, n+2, l0) | ptr l0) = let
  prval () = lemma_at_view (pf_hd)
  prval () = lemma_at_view (pf_v) 
in
  if ptr1_isneqz (p1) then let
    prval slseg_v_cons (pf_nhd, pf_nlst) = pf_lst
    prval (pf_nhd_at, fpf_nhd_at) = slnode_v_takeout (pf_nhd)
    val found = slist_insert_before$pred<a> (!p1)
    prval pf_nhd = fpf_nhd_at (pf_nhd_at)
  in
    if found then let
      val () = slist_node_set_next<a> (pf_hd | p0, pv)
      val () = slist_node_set_next<a> (pf_v | pv, p1)
      prval pf_lst = slseg_v_cons (pf_nhd, pf_nlst)
      prval pf_res = slseg_v_cons (pf_hd, slseg_v_cons (pf_v, pf_lst))
    in
      (pf_res | p0)
    end else let
      val p2 = slist_node_get_next<a> (pf_nhd | p1)
      val (pf_lst | p_lst) = aux (pf_v, pf_nhd, pf_nlst | pv, p1, p2)
      prval pf_lst = slseg_v_cons (pf_hd, pf_lst)
    in
      (pf_lst | p0)
    end
  end else let
    // insert after the current tail, since there is no element found
    prval slseg_v_nil () = pf_lst
    val () = slist_node_set_next<a> (pf_hd | p0, pv)
    val () = slist_node_set_next<a> (pf_v | pv, the_null_ptr)
    prval pf_res = slseg_v_cons (pf_hd, slseg_v_cons (pf_v, slseg_v_nil ()))
  in
    (pf_res | p0)
  end
end
//
prval pf_sl = sl.0
val p_sl = sl.1
prval pf_v = slnode_v_intr (pf_v)
prval () = lemma_at_view (pf_v) 
val new_sl =
  (if ptr1_isneqz (p_sl) then let
    prval slseg_v_cons (pf_hd, pf1_sl) = pf_sl
    //
    prval (pf_hd_at, fpf_hd_at) = slnode_v_takeout (pf_hd)
    val found = slist_insert_before$pred<a> (!p_sl)
    prval pf_hd = fpf_hd_at (pf_hd_at)
    //
  in
    if found then let
      val () = slist_node_set_next<a> (pf_v | p, p_sl)
      prval pf_sl = slseg_v_cons (pf_hd, pf1_sl)
      prval pf_list = slseg_v_cons (pf_v, pf_sl)
    in
      (pf_list | p)
    end else let
      val p_next = slist_node_get_next<a> (pf_hd | p_sl)
    in
      aux (pf_v, pf_hd, pf1_sl | p, p_sl, p_next)
    end
  end else let
    prval slseg_v_nil () = pf_sl
    val () = slist_node_set_next<a> (pf_v | p, the_null_ptr)
    prval () = lemma_at_view (pf_v)    
    prval pf = slseg_v_cons (pf_v, slseg_v_nil ())
  in
    (pf | p)
  end) : slist (a, n+1)
prval () = sl.0 := new_sl.0
val () = sl.1 := new_sl.1
//
}
