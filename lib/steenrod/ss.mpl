# This file is about Singer systems of endomorphisms of the additive formal
# group.  Such a system has groups G(i,j) (for 0 <= i <= j <= n say),
# all of which are equal to the standard additive formal group.  There
# are morphisms G(j,k) -> G(i,l) whenever i <= j <= k <= l, with the
# evident functoriality condition.  The horizontal maps are linear
# and the vertical maps are short isogenies.  Every equal-length
# L-shaped subdiagram is like G -> G/a <- G//a for some a.



aa := proc(i::nonnegint,k::nonnegint)
 if i > k then return FAIL; fi;
 return v[k] * mul(v[t]^(2^(k-t-1)),t=i..k-1);
end:

bb := proc(i::nonnegint,k::nonnegint)
 if i > k then return FAIL; fi;
 return v[i-1]^(2^(k-i));
end:

# G(i,k) to G(i-1,k)
pp := (i,k) -> (x) -> bb(i,k) * x:

# G(i,k) to G(i,k+1)
qq := (i,k) -> (x) -> aa(i,k) * x + x^2:

# G(j,k) to G(i,k)
ppp := proc(i,j,k)
 local x,y,z;

 if i > j then 
  return FAIL;
 elif i = j then 
  return (x -> x);
 else
  y := ppp(i+1,j,k)(x);
  z := collect(modp(expand(pp(i+1,k)(y)),2),x);
  return unapply(z,x);
 fi;
end:

# G(j,k) to G(i,k)
ppp1 := proc(i,j,k) local x; unapply(mul(v[m]^(2^(k-m-1)),m=i..j-1) * x,x); end:
 
# G(i,k) to G(i,l)
qqq := proc(i,k,l)
 local x,y,z;

 if k > l then 
  return FAIL;
 elif l = k then 
  return (x -> x);
 else
  y := qqq(i,k,l-1)(x);
  z := collect(modp(expand(qq(i,l-1)(y)),2),x);
  return unapply(z,x);
 fi;
end:

W0V := (k) -> mul(V[i],i=0..k-1):

WW := proc(k,l,m)
  local J,P;
  J := [seq(j,j=k..l-1)];
  P := combinat[choose](J,l-k-m);
  return add(mul(V[u[t]]^(2^(k+m+t-1-u[t])),t=1..l-k-m),u in P);
end: 

WWW := (j,k,l,m) -> WW(k,l,m) * W0V(j)^(2^(k+m-j) - 2^(l-j)):

WWWW := (i,j,k,l,m) -> WW(k,l,m) * W0V(j)^(2^(k+m-j)) / W0V(i)^(2^(l-i)):

# G(i,k) to G(i,l)
qqq1 := proc(j,k,l)
 local x;
 return unapply(sort(collect(expand(add(WWW(j,k,l,i) * x^(2^i),i=0..l-k)),x)),x):
end:

# G(j,k) to G(i,l)
ff := proc(i,j,k,l)
 local x;
 return unapply(sort(collect(expand(add(WWWW(i,j,k,l,m) * x^(2^m),m=0..l-k)),x)),x):
end:
 
vV_rule := {seq(v[i]=V[i]/W0V(i),i=0..100)}:
