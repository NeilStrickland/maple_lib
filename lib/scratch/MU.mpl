make_fgl_Lazard := proc(d)
 global a,m,ma,am;
 local T,u,x,y,q,i,k,Fm,sol;

 T := table();
 T["degree"] := d;
 Order := d+2;

 T["log_m"] := unapply(x + add(m[i]*x^(i+1),i=1..d-1),x);
 T["exp_m"] := 
   unapply(
   convert(
    solve(x = series(T["log_m"](y) + sin(y)^(d+1),y=0,d+1),y),
    polynom,x
   ),
   x
  );

 T["sum_m"] :=
  unapply(
   subs(u=1,expand(convert(series(T["exp_m"](T["log_m"](u*x)+T["log_m"](u*y)),u=0,d+1),polynom,u))),
   x,y
  ):

 Fm := T["sum_m"](x,y);
 am[1] := m[1];
 for k from 2 to d-1 do
  q := igcd_alt([seq(binomial(k+1,i),i=1..k)])[2];
  am[k] := -add(q[i]*coeff(coeff(Fm,x,i),y,k+1-i),i=1..k);
 od:
 sol := solve({seq(a[i]=am[i],i=1..d-1)},{seq(m[i],i=1..d-1)}):
 for i from 1 to d-1 do ma[i] := subs(sol,m[i]); od:

 T["log_a"] := unapply(collect(expand(eval(subs(m = ma,T["log_m"](x)))),x),x);
 T["exp_a"] := unapply(collect(expand(eval(subs(m = ma,T["exp_m"](x)))),x),x);
 T["sum_a"] := unapply(collect(expand(eval(subs(m = ma,T["sum_m"](x,y)))),{x,y}),x,y);

 return eval(T);
end:

