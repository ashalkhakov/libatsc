
prfun
array_v_split_at
  {a:vtflt}
  {l:addr}
  {n:int}{i:nat | i <= n}
(
  pfarr: array_v (INV(a), l, n) | i: size (i)
) :<prf> @(
  array_v (a, l, i), array_v (a, l+i*sizeof(a), n-i)
) // end of [array_v_split_at]

prfun
array_v_unsplit
  {a:vtflt}
  {l:addr}
  {n1,n2:int}
(
  pf1arr: array_v (INV(a), l, n1)
, pf2arr: array_v (a, l+n1*sizeof(a), n2)
) :<prf> array_v (a, l, n1+n2) // end of [array_v_unsplit]

prfun
array_v_extend :
  {a:vtflt}
  {l:addr}{n:int}
  (array_v (INV(a), l, n), a @ l+n*sizeof(a)) -<prf> array_v (a, l, n+1)

prfun
array_v_unextend :
  {a:vtflt}
  {l:addr}
  {n:int | n > 0}
  (array_v (INV(a), l, n)) -<prf> (array_v (a, l, n-1), a @ l+(n-1)*sizeof(a))
