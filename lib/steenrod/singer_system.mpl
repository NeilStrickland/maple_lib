# This file is about Singer systems of endomorphisms of the additive formal
# group.  Such a system has groups G(i,j) (for 0 <= i <= j <= n say),
# all of which are equal to the standard additive formal group.  There
# are morphisms G(j,k) -> G(i,l) whenever i <= j <= k <= l, with the
# evident functoriality condition.  The horizontal maps are linear
# and the vertical maps are short isogenies.  Every subdiagram
# G(i,i) -> G(i,j) <- G(j,j) is of the form G -> G/a <- G//a.

W0V := (k) -> mul(V[i],i=0..k-1):

WW := proc(k,l,m)
  local J,P;
  J := [seq(j,j=k..l-1)];
  P := combinat[choose](J,l-k-m);
  return add(mul(V[u[t]]^(2^(k+m+t-1-u[t])),t=1..l-k-m),u in P);
end: 

WWW := (i,j,k,l,m) -> WW(k,l,m) * W0V(j)^(2^(k+m-j)) / W0V(i)^(2^(l-i)):

# G(j,k) to G(i,l)
f := proc(i,j,k,l)
 local x;
 return unapply(sort(collect(expand(add(WWW(i,j,k,l,m) * x^(2^m),m=0..l-k)),x)),x):
end:

vV_rule := {seq(v[i]=V[i]/W0V(i),i=0..20)}:

Vv_rule := {seq(
 V[i] = v[i] * mul(v[j]^(2^(i-j-1)),j=0..i-1),
 i=0..20)};

check_id := proc(i::nonnegint,k::nonnegint)
 local x;

 if not (i <= k) then return FAIL; fi;
 
 _ASSERT(f(i,i,k,k)(x) = x,"identity maps",[i,k]);
 
end:

check_compose := proc(h::nonnegint,i::nonnegint,j::nonnegint,
                      k::nonnegint,l::nonnegint,m::nonnegint)
 local x,err;

 if not(h <= i and i <= j and j <= k and k <= l and l <= m) then
  return FAIL;
 fi;

 err := modp(expand(f(h,i,l,m)(f(i,j,k,l)(x)) - f(h,j,k,m)(x)),2);

 _ASSERT(err = 0,"maps compose correctly",[h,i,j,k,l]);
end: 

check_linear := proc(i::nonnegint,j::nonnegint,k::nonnegint)
 local x,y,err;

 if not(i <= j and j <= k) then
  return FAIL;
 fi;

 y := f(i,j,k,k)(x);
 err := expand(y - coeff(y,x,1) * x);

 _ASSERT(err = 0,"horizontal map is linear",[i,j,k]);
end:

check_short_isogeny := proc(i::nonnegint,k::nonnegint,l::nonnegint)
 local x,y,err;

 if not(i <= k and k <= l) then
  return FAIL;
 fi;

 y := f(i,i,k,l)(x);
 
 _ASSERT(degree(y,x) = 2^(l-k) and coeff(y,x,2^(l-k)) = 1,
         "vertical map is a short isogeny",[i,k,l]);
end:

check_dilation := proc(i::nonnegint,p::nonnegint)
 local x,y,z,err;

 y := f(i,i,i,i+p)(x);
 z := f(i,i+p,i+p,i+p)(x);
 _ASSERT(expand(coeff(y,x,1) - coeff(z,x,1)) = 0,"dilation condition",[i,j,k]);
end:

check_vV_rules := proc(n)
 _ASSERT(
  `and`(seq(evalb(subs(vV_rule,subs(Vv_rule,V[i])) = V[i]),i=0..n)) and
  `and`(seq(evalb(subs(Vv_rule,subs(vV_rule,v[i])) = v[i]),i=0..n)),
  "rules for converting v[i] to V[i] and vice versa"
 );
 
end:

