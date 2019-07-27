
fun
memmove_right {a:vtflt}{l:addr;n,k:nat} (
  pf_arr: array_v(a, l, n)
, pf_buf: array_v(a?, l+n*sizeof(a), k)
| dst: ptr (l+k*sizeof(a)), src: ptr l, nb: size(n*sizeof(a))
): (
  array_v(a?, l, k), array_v (a, l+k*sizeof(a), n)
| ptr (l+k*sizeof(a))
) = "mac#memmove"

fun
memmove_left {a:vtflt}{l:addr;n,k:nat} (
  pf_buf: array_v(a?, l, k)
, pf_arr: array_v(a, l+k*sizeof(a), n)
| dst: ptr (l), src: ptr (l+k*sizeof(a)), nb: size(n*sizeof(a))
): (
  array_v(a, l, n), array_v (a?, l+n*sizeof(a), k)
| ptr (l-k*sizeof(a))
) = "mac#memmove"

fun
memcpy {a:vtflt;l1,l2:addr;n:nat} (
  pf1_arr: array_v (a, l1, n)
, pf2_arr: array_v (a?, l2, n)
| dst: ptr l2, src: ptr l1, nb: size(n*sizeof(a))
): (
  array_v (a?, l1, n)
, array_v (a, l2, n)
| ptr l2
) = "mac#memcpy"

fun
memcpy_tflt {a:tflt;l1,l2:addr;n:nat} (
  pf1_arr: array_v (a, l1, n)
, pf2_arr: array_v (a?, l2, n)
| dst: ptr l2, src: ptr l1, nb: size(n*sizeof(a))
): (
  array_v (a, l1, n)
, array_v (a, l2, n)
| ptr l2
) = "mac#memcpy"
