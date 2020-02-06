#@ Not autoload

MU_n_max := 10;

make_fgl_Lazard := proc(d)
 global a,m,ma,am;
 local e,T,u,x,y,q,i,j,k,Fm,Fmp,err,sol;

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

 Fm := x+y;
 for k from 2 to d do
  Fmp[0] := 1;
  Fmp[1] := subs({x=e*x,y=e*y},Fm);
  for j from 2 to k do
   Fmp[j] := rem(expand(Fmp[1] * Fmp[j-1]),e^(k+1),e);
  od;
  err := expand(Fmp[1] - e*x - e*y +
   add(m[i]*(Fmp[i+1] - e^(i+1)*(x^(i+1)+y^(i+1))),i=1..k-1));
  Fm := Fm - subs(e=1,err);
 od:
 
 T["sum_m"] := unapply(Fm,x,y):

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

MU_vars := plex(seq(a[i],i=1..MU_n_max));
MUMU_vars := plex(seq(a[i],i=1..MU_n_max),seq(b[i],i=1..MU_n_max));