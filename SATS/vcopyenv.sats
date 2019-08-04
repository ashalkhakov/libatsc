viewdef
vtakeout
( v1: view
, v2: view ) = (v2, v2 -<lin,prf> v1)
viewdef
vtakeout0 (v:view) = vtakeout(void, v)

praxi
vcopyenv_v_decode
  {v:view}(x: vcopyenv_v(v)): vtakeout0(v)
