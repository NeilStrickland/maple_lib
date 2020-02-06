# This checks some formulae in the LaTeX file Out_SL2.tex

check_aut_SL2 := proc()
 local i2,alpha,beta,beta0,gamma,mu,sigma,rho,
  m,n,g,h,a,b,c,d,t,u,v,rels,
  is_in_U,is_in_T,is_in_B,err;

 i2 := IdentityMatrix(2);
 alpha := (v) -> <<1|v>,<0|1>>;
 mu := (u) -> <<u|0>,<0|1/u>>;
 
 is_in_U := (g) -> g[2,1] = 0 and g[1,2] = 0 and g[1,1] * g[2,2] = 1;
 is_in_T := (g) -> g[2,1] = 0 and g[1,1] = 1 and g[2,2] = 1;
 is_in_B := (g) -> g[2,1] = 0 and g[1,1] * g[2,2] = 1;
 rho := (u) -> g[1,1];
 sigma := (a) -> <<0|1>,<1|a>>;
 beta := (a,b) -> alpha(b) . sigma(a) . (1/alpha(b)) . (1/sigma(a));
 beta0 := (b) -> <<1+b^2|b>,<b|1>>;
 gamma := (b,u) -> <<1/u|0>,<(1+b^2)/u|u>>;

 _ASSERT(
  Equal(map(modp,simplify(beta(a,b)),2),beta0(b)),
  "Formula for beta(b)"
 ):
 
 err := gamma(b,u).beta0(b).(1/gamma(b,u)) - sigma(b^2);
 err := map(modp,simplify(subs(b = u^2,err)),2);
 _ASSERT(
  Equal(err,<<0|0>,<0|0>>),
  "beta(b) is conjugate to sigma(b^2)"
 ):

 m := <<1/u|0>,<0|u>>;
 n := <<u|u>,<0|1/u>>;
 _ASSERT(
  Equal(m.n,alpha(1)),
  "m n = alpha(1)"
 );

 g := <<a|b>,<c|d>>;
 g := subs(solve(map(op,convert(g.alpha(1) - alpha(1).g,listlist)),{c,d}),g);
 _ASSERT(
  Equal(g,<<a|b>,<0|a>>),
  "Centraliser of alpha(1)"
 );

 g := <<u|v>,<0|1/u>>;
 h := alpha(v/(1/u-u));
 _ASSERT(
  Equal(simplify(h.mu(u).(1/h)),g),
  "D_u is conjugate to mu(u) in B"
 );

 g := <<a|b>,<c|d>>;
 rels := map(numer,map(op,convert(mu(u).g.mu(u).g - i2,listlist)));
 rels := map(coeffs,expand(rels),u);
 g := subs(solve(rels,{a,c,d}),g);
 _ASSERT(
  Equal(g,<<0|b>,<1/b|0>>),
  "(mu(u) . g)^2 = 1 only on U"
 );

 _ASSERT(
  Equal(mu(u) . alpha(t) . (1/mu(u)),alpha(u^2*t)),
  "Conjugate of alpha(t) by mu(u)"
 );
end:
