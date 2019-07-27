#staload "libats/SATS/gint.sats"
#staload "libats/SATS/gptr.sats"

#staload UN = "libats/SATS/unsafe.sats"

#staload "./../SATS/pointer.sats"

impltmp
{a}//tmp
ptr1_add{l,n}(p0, n0) =
$UN.cast{ptr(l+n*sizeof(a))}(g0add_ptr_size(p0, n0*sizeof<a>))

impltmp
{}//tmp
ptr1_isneqz{l}(p0) =
$UN.cast{bool(l>null)}(ptr0_isneqz(p0))
