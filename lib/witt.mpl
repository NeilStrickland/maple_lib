DV := NumberTheory[Divisors]:

ghost_coeff := (n) -> (x) -> 
 add(d * x[d]^(n/d), d in DV(n));

ghost_vector := (n::posint) -> (x) -> [seq(ghost_coeff(m)(x),m=1..n)];

unghost_vector := (n::posint) -> proc(w)
 local x,m;
 x := []:
 for m from 1 to n do 
  x := [op(x),expand((w[m] - add(d*x[d]^(m/d),d in DV(m) minus {m}))/m)];
 od:
 return x;
end:

witt_add_term := proc(n::posint) 
 option remember;
 local x,y,u,d,rel;
 
 for d in DV(n) minus {n} do
  u[d] := witt_add_term(d)(x,y);
 od:

 rel := ghost_coeff(n)(u) - ghost_coeff(n)(x) - ghost_coeff(n)(y);
 u[n] := expand(solve(rel,u[n]));
 return unapply(u[n],x,y);
end:

witt_add := (n::posint) -> (x,y) -> [seq(witt_add_term(m)(x,y),m=1..n)];

witt_mult_term := proc(n::posint) 
 option remember;
 local x,y,u,d,rel;
 
 for d in DV(n) minus {n} do
  u[d] := witt_mult_term(d)(x,y);
 od:

 rel := ghost_coeff(n)(u) - ghost_coeff(n)(x) * ghost_coeff(n)(y);
 u[n] := expand(solve(rel,u[n]));
 return unapply(u[n],x,y);
end:

witt_mult := (n::posint) -> (x,y) -> [seq(witt_mult_term(m)(x,y),m=1..n)];

witt_series := (n::posint) -> (x) -> expand(rem(mul(1 - x[m]*t^m,m=1..n),t^(n+1),t));

witt_unseries := (n::posint) -> proc(f)
 local c,g,d;
 c := []:
 g := f;
 for d from 1 to n do
  c := [op(c),-coeff(g,t,d)];
  g := expand(convert(series(g/(1-c[d]*t^d),t=0,n+1),polynom,t));
 od:
 return c; 
end:

ghost_p_coeff := (n) -> (x) -> 
 add(p^i * x[i]^(p^(n-i)), i=0..n);
ghost_p_vector := (n::nonnegint) -> (x) -> 
 table([seq(i = ghost_p_coeff(i)(x),i=0..n-1)]);
ghost_p_add := (n::nonnegint) -> (a,b) ->
 table([seq(i=expand(a[i]+b[i]),i=0..n-1)]);
ghost_p_sub := (n::nonnegint) -> (a,b) ->
 table([seq(i=expand(a[i]-b[i]),i=0..n-1)]);
ghost_p_mult := (n::nonnegint) -> (a,b) ->
 table([seq(i=expand(a[i]*b[i]),i=0..n-1)]);
ghost_p_is_equal := (n::nonnegint) -> (a,b) ->
 `and`(seq(evalb(simplify(a[i]-b[i])=0),i=0..n-1));

unghost_p_vector := (n::nonnegint) -> proc(w)
 local x,m;
 x := table:
 for m from 0 to n-1 do 
  x[m] := expand((w[m] - add(p^k*x[k]^(p^(m-k)),k=0..m-1))/p^m);
 od:
 return eval(x);
end:

witt_p_add_term := proc(n::nonnegint) 
 option remember;
 local x,y,u,m,rel;
 u := table():
 for m from 0 to n-1 do
  u[m] := witt_p_add_term(m)(x,y);
 od:

 rel := ghost_p_coeff(n)(u) - ghost_p_coeff(n)(x) - ghost_p_coeff(n)(y);
 u[n] := expand(solve(rel,u[n]));
 return unapply(u[n],x,y);
end:

witt_p_add := (n::posint) -> (x,y) -> table([seq(m=witt_p_add_term(m)(x,y),m=0..n-1)]);

witt_p_mult_term := proc(n::nonnegint) 
 option remember;
 local x,y,u,m,rel;
 u := table():
 for m from 0 to n-1 do
  u[m] := witt_p_mult_term(m)(x,y);
 od:

 rel := ghost_p_coeff(n)(u) - ghost_p_coeff(n)(x) * ghost_p_coeff(n)(y);
 u[n] := expand(solve(rel,u[n]));
 return unapply(u[n],x,y);
end:

witt_p_mult := (n::posint) -> (x,y) -> table([seq(m=witt_p_mult_term(m)(x,y),m=0..n-1)]);
