
fun
{a:vtflt}
ptr1_add
{l:addr;n:uint}(ptr(l), n: size(n)):<> ptr(l+n*sizeof(a))

fun{}
ptr1_isneqz
{l:addr}(ptr(l)):<> bool(l>null)

castfn
ref_make_viewptr
  {a:vtflt}{l:addr}
  (pf: a @ l | p: ptr(l)):<> ref(a)
// end of [ref_make_viewptr]


fun
{a:vtflt}
array_ptr_takeout
  {l:addr}{n:int}{i:nat | i < n}
(
  array_v (INV(a), l, n) | ptr l, size i
) : (
  a @ (l+i*sizeof(a))
, a @ (l+i*sizeof(a)) -<lin,prf> array_v (a, l, n)
| ptr (l+i*sizeof(a))
) (* end of [array_ptr_takeout] *)
