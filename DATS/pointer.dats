#staload "libats/SATS/gint.sats"
#staload "libats/SATS/gptr.sats"

#staload UN = "libats/SATS/unsafe.sats"

#staload "./../SATS/array_prf.sats"

#staload "./../SATS/pointer.sats"

impltmp
{a}//tmp
ptr1_add{l,n}(p0, n0) =
$UN.cast{ptr(l+n*sizeof(a))}(g0add_ptr_size(p0, n0*sizeof<a>))

impltmp
{}//tmp
ptr1_isneqz{l}(p0) =
$UN.cast{bool(l>null)}(ptr0_isneqz(p0))

impltmp{a}
ptr_write0 (pf | p, x) = !p := x

impltmp{a}
ptr_write (pf | p, x) = !p := x
impltmp{a}
ptr_read (pf | p) = !p

impltmp
{a}//tmp
array_ptr_takeout
  {l}{n}{i} (pf_arr | p_arr, i) =
(pf, fpf | ptr1_add<a>(p_arr, i))
where {
  prval (pf, fpf) = array_v_takeout{a}{l}{n}{i}(pf_arr)
}
