######################################################################

`eta/simplex_interior` :=
 (A::set) -> `if`(nops(A)=1,table({op(A)=1}),FAIL);

`gamma/simplex_interior` := (A::set,B::set) -> (p) -> proc(y,x)
 local a;
 return table({seq(a = x[p[a]][a] * y[p[a]],a in A)});
end:

