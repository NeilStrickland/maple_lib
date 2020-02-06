# This makes the formal group law for integral Morava K-theory
# We truncate powers d+1 and higher

make_fgl_Morava := proc(p,n,d)
 local T,ld,x,y,u;

 T := table();
 T["p"] := p;
 T["n"] := n;
 T["d"] := d;
 T["height"] := n;
 T["degree"] := d;

 ld := 0;
 while p^ld <= d/p do ld := ld+1; od;
 T["log_degree"] := ld;
 
 T["log"] := unapply(add(x^(p^(n*i))/p^i,i=0..ld),x);
 T["p_series"] := unapply(x^(p^n),x);

 Order := d+2;
 
 T["exp"] :=
  unapply(
   convert(
    solve(x = series(T["log"](y) + sin(y)^(d+1),y=0,d+1),y),
    polynom,x
   ),
   x
  );

 T["p_series"] := 
  unapply(expand(convert(series(T["exp"](p*T["log"](x)),x=0,d+1),polynom,x)),x);

 T["sum"] :=
  unapply(
   subs(u=1,expand(convert(series(T["exp"](T["log"](u*x)+T["log"](u*y)),u=0,d+1),polynom,u))),
   x,y
  ):

 T["sum0"] := unapply(mods(T["sum"](x,y),p),x,y);
 T["p_series0"] := unapply(mods(T["p_series"](x),p),x);

 return eval(T);
end:
