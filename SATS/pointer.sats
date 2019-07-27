
fun
{a:vtflt}
ptr1_add
{l:addr;n:uint}(ptr(l), n: size(n)):<> ptr(l+n*sizeof(a))

fun{}
ptr1_isneqz
{l:addr}(ptr(l)):<> bool(l>null)
