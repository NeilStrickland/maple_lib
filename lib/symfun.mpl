# This function assumes that u is a symmetric polynomial in 
# x[1],...,x[n] and returns a polynomial in c[1],...,c[n] 
# that agrees with u after replacing the variables c[i] by
# the elementary symmetric functions in x[1],...,x[n].
# If the optional argument p_ is supplied, then the calculation
# is done mod p_.

newton_rewrite := proc(u,n,x,c,p_)
 local p,f,i,v,w,a,m,k,cx,cxp,vars;

 p := `if`(nargs > 4,p_,0);

 f := expand(mul(t+x[i],i=1..n));
 for i from 1 to n do 
  cx[i] := coeff(f,t,n-i);
 od:

 cxp := proc(i,j)
  option remember;
  local u;

  if j = 0 then
   return 1;
  else
   u := expand(cx[i]*cxp(i,j-1));
   if p > 0 then u := mods(u,p); fi;
   return u;   
  fi;
 end:

 v := u;
 w := 0;
 vars := plex(seq(x[i],i=1..n));
 while v <> 0 do
  a,m := LeadingTerm(v,vars);
  k := [seq(degree(m,x[i]),i=1..n),0];
  w := w + a * mul(c[i]^(k[i]-k[i+1]),i=1..n);
  v := expand(v - a * mul(cxp(i,k[i]-k[i+1]),i=1..n));
  if nargs > 4 then v := modp(v,p_); fi;
 od:

 return w;
end:

orbit_sum := proc(m,n,x)
 local S,R,v,C,c,r,i;
 S := combinat[permute](n);
 R := map(s -> [seq(x[i]=x[s[i]],i=1..n)],S);
 v := add(subs(r,m),r in R);
 C := {coeffs(v,{seq(x[i],i=1..n)})};
 c := igcd(op(C));
 v := expand(v/c);
 return v;
end: