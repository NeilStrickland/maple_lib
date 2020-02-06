`is_element/sphere` := (N::nonnegint) -> proc(x)
 local err;

 if not `is_element/R`(N+1)(x) then
  return false;
 fi;

 err := simplify(add(x[i]^2,i=1..N+1) - 1);
 return evalb(err = 0);
end:

`is_equal/sphere` := (N::nonnegint) -> (x,y) -> evalb(simplify(x -~ y) = [0$(N+1)]);

`is_leq/sphere` := NULL;
`list_elements/sphere` := NULL;
`count_elements/sphere` := NULL;

`random_element/sphere` := (N::nonnegint) -> proc(d::posint := 5)
 local r,x,n,k,e;

 r := rand(-d..d);
 x := [seq(r(),i=1..N)];
 n := add(x[i]^2,i=1..N);
 x := x *~ (2/(1+n));
 k := rand(0..N)();
 e := (-1) ^ rand(0..1)(); # only really needed for N = 0
 x := e *~ [op(1..k,x),(1-n)/(1+n),op(k+1..N,x)];
 return x;
end: 