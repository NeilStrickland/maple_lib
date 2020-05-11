######################################################################

`eta/prime_simplex` := (A::set) -> `if`(nops(A)=1,table({op(A)=1}),FAIL);

`gamma/prime_simplex` := (A::set,B::set) -> (p) -> (y,x) -> 
  table({seq(a = x[p[a]][a] * y[p[a]],a in A)});

`gamma_min/prime_simplex` := (A::set,B::set) -> (p) -> (y,x) -> 
  table({seq(a = min(x[p[a]][a] , y[p[a]]),a in A)});
