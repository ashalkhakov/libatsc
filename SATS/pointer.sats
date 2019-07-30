
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
