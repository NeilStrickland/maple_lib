A_infinity_rel := (m) -> proc(n::posint)
 local p,r,s,t,u;
 p := 0;
 for r from 0 to n do
  for s from 1 to n-r do
   t := n - r - s;
   u := r + 1 + t;
   p := p + (-1)^(r+s*t) *
    m(u)(seq(x[i],i=1..r),
      m(s)(seq(x[i],i=r+1..r+s)),
      seq(x[i],i=r+s+1..n));
  od;
 od;
 return unapply(p,seq(x[i],i=1..n));
end:

A_infinity_deg := (n) -> n - 2;

twisted_complex_rel := (d) -> (u) -> 
 unapply(add((-1)^i * d(i)(d(u-i)(x)),i=0..u),x);

twisted_complex_bideg := (i) -> [i,i-1];

DA_infinity_rel := (mm) -> proc(i::nonnegint,n::posint) 
 local p,r,s,t,u,j,k,x;
 p := 0;
 for r from 0 to n do
  for s from 1 to n-r do
   for j from 0 to i do
    t := n - r - s;
    u := r + 1 + t;
    k := i - j;
    p := p + (-1)^(r*s+t+k*u) *
     mm(j,u)(seq(x[l],l=1..r),
       mm(k,s)(seq(x[l],l=r+1..r+s)),
       seq(x[l],l=r+s+1..n));
   od;
  od;
 od;
 return unapply(p,seq(x[l],l=1..n));
end:

DA_infinity_bideg := (i,n) -> [i,i+n-2];

