`is_element/E/subdiv` := (p::nonnegint,n::nonnegint,m::nonnegint) -> proc(theta)
 global reason;
 local tag,src,tgt,i,t;
 tag := "is_element/E/subdiv";

 if p = 0 then
  return evalb(n = m and theta = []);
 fi;

 if not(type(theta,list(list(nonnegint)))) then
  reason := [tag,"theta is not a list of lists of natural numbers",theta];
  return false;
 fi;

 if nops(theta) <> p then
  reason := [tag,"theta is not a list of length p",theta,p];
  return false;
 fi;

 tgt := NULL;
 for i from 1 to p do
  if theta[i] = [] then
   reason := [tag,"theta[i] is empty",theta,i];
   return false;
  fi;
  t := max(op(theta[i]));
  if {op(theta[i])} <> {seq(j,j=0..t)} then
   reason := [tag,"theta[i] does not give an epimorphism",theta,i,t];
   return false;
  fi;
  tgt := tgt,t;
 od:
 tgt := [tgt];

 src := map(nops,theta) -~ 1;

 if src[1] <> n then
  reason := [tag,"chain does not start with [n]",theta,src,n];
  return false;
 fi;

 if tgt[p] <> m then
  reason := [tag,"chain does not end with [m]",theta,tgt,m];
  return false;
 fi;
 
 if [op(src),m] <> [n,op(tgt)] then
  reason := [tag,"sources and targets do not match",theta,src,tgt,n,m];
  return false;
 fi;

 return true;
end:

`is_leq/E/subdiv` := NULL;

`list_elements/E/subdiv/aux` := proc(n::nonnegint,m::nonnegint)
 option remember;
 local N,M,E;

 N := {seq(i,i=0..n)};
 M := {seq(i,i=0..m)};
 E := `list_elements/epi`(N,M);
 E := map(f -> [seq(f[i],i=0..n)],E);
 return E;
end:

`list_elements/E/subdiv` := proc(p::nonnegint,n::nonnegint,m::nonnegint)
 option remember;
 local L,k,E0,E1;

 if p = 0 then
  if n = m then
   return [[]];
  else
   return [];
  fi;
 else
  L := NULL;
  for k from m to n do
   E0 := `list_elements/E/subdiv`(p-1,n,k);
   E1 := `list_elements/E/subdiv/aux`(k,m);
   L := L,seq(seq([op(e0),e1],e1 in E1),e0 in E0);
  od:
 fi;
 return [L];
end:

`random_element/E/subdiv` := (p::nonnegint,n::nonnegint,m::nonnegint) -> proc()
 local k,q,f,g;
 
 if m > n then
  return FAIL;
 fi;

 if p = 0 then
  if m = n then
   return [];
  else
   return FAIL;
  fi;
 elif p = 1 then
  g := `random_element/epi`({seq(j,j=0..n)},{seq(j,j=0..m)})();
  return [[seq(g[j],j=0..n)]]; 
 else
  k := rand(m..n)();
  q := rand(1..p-1)();
  f := `random_element/E/subdiv`(q,n,k)();
  g := `random_element/E/subdiv`(p-q,k,m)();
  return [op(f),op(g)];
 fi;
end:

`count_elements/E/subdiv` := proc(p::nonnegint,n::nonnegint,m::nonnegint)
 option remember;
 if p = 0 then
  return `if`(n = m,1,0);
 else
  return add(`count_elements/E/subdiv`(p-1,n,k) *
             Stirling2(k+1,m+1) * (m+1)!,k=m..n);
 fi;
end:

`degrees/E/subdiv` := (p,n,m) -> (theta) ->
 [op(map(nops,theta) -~ 1),m];

######################################################################

`is_element/EE/subdiv` := (p::nonnegint,n::nonnegint) -> proc(theta)
 global reason;
 local tag,src,tgt,i,m,t,b;
 tag := "is_element/EE/subdiv";

 if p = 0 then
  if theta = [] then
   return true;
  else
   reason := [tag,"for p=0 the only element is []",theta];
   return phi;
  fi;
 fi;

 if not(type(theta,list(list(nonnegint)))) then
  reason := [tag,"theta is not a list of lists of natural numbers",theta];
  return false;
 fi;

 if nops(theta) <> p then
  reason := [tag,"theta is not a list of length p",theta,p];
  return false;
 fi;

 if theta[p] = [] then
  reason := [tag,"theta[p] = []",theta,p];
  return false;
 fi;

 m := max(op(theta[p]));
 
 b := `is_element/E/subdiv`(p,n,m)(theta);
 if not(b) then
  reason := [tag,"is_element/E/subdiv failed",m,reason];
  return false;
 fi;

 return true;
end:

`is_leq/EE/subdiv` := NULL;

`list_elements/EE/subdiv` := proc(p::nonnegint,n::nonnegint)
 option remember;
 [seq(op(`list_elements/E/subdiv`(p,n,m)),m=0..n)];
end:

`random_element/EE/subdiv` := (p::nonnegint,n::nonnegint) -> proc()
 local m;
 m := rand(0..n)();
 return `random_element/E/subdiv`(p,n,m)();
end:

`count_elements/EE/subdiv` := proc(p::nonnegint,n::nonnegint)
 add(`count_elements/E/subdiv`(p,n,m),m=0..n);
end:

`find_count_coeffs/EE/subdiv` := proc(n)
 local E,a,p,k;
 E := [seq(`count_elements/EE/subdiv`(p,n) - add((-1)^(n+k)*a[n,k]*((k+1)!)^p,k=0..n),p=1..n+5)];
 return solve(E);
end:

`degrees/EE/subdiv` := (p,n) -> (theta) ->
 [op(map(nops,theta) -~ 1),max(op(theta[p]))];

######################################################################

`is_element/threads/subdiv` := (p::nonnegint,n::nonnegint) -> (theta) -> proc(i)
 global reason;
 local tag,k,m;

 tag := "is_element/threads/subdiv";
 
 if not(type(i,list(nonnegint)) and nops(i) = p+1) then
  reason := [tag,"i is not a list of p+1 natural numbers",i,p];
  return false;
 fi;

 k := `degrees/EE/subdiv`(p,n)(theta);
 
 for m from 0 to p do
  if i[m+1] > k[m+1] then
   return false;
  fi;
   
  if m < p and theta[m+1][i[m+1]+1] > i[m+2] then
   return false;
  fi;
 od:

 return true;
end:

`is_leq/threads/subdiv` := NULL;

`list_elements/threads/subdiv` := (p::nonnegint,n::nonnegint) -> proc(theta)
 local i,k,m,phi,L,M;

 if p = 0 then
  return [seq([i],i=0..n)];
 else
  m := max(op(theta[p]));
  phi := [op(1..p-1,theta)];
  L := `list_elements/threads/subdiv`(p-1,n)(phi);
  M := NULL;
  for i in L do
   k := theta[p][i[p]+1];
   M := M,seq([op(i),j],j=k..m);
  od:
  return [M];
 fi;
end:

`random_element/threads/subdiv` := (p::nonnegint,n::nonnegint) -> (theta) -> proc()
 local i,j,k,m0,m1;

 k := `degrees/EE/subdiv`(p,n)(theta);
 i := [rand(0..n)()];
 for j from 1 to p do
  m0 := theta[j][i[j]+1];
  m1 := k[j+1];
  i := [op(i),rand(m0..m1)()];
 od;
 
 return i;
end:

`count_elements/threads/subdiv` := NULL;

`mu/threads/subdiv` := (p::nonnegint,n::nonnegint) -> (theta) -> proc(i)
 local k,u,m;
 
 k := `degrees/EE/subdiv`(p,n)(theta);

 u := k[p+1]+1;
 for m from 0 to p-1 do
  u := u * nops(select(j -> (j <= i[m+2]),theta[m+1]));
 od:

 return u;
end:

`xi/EE/subdiv` := (p::nonnegint,n::nonnegint) -> proc(theta)
 local x,II,i;
 
 if p = 0 then
  return [1$(n+1)]/~(n+1);
 fi;
 
 x := table([seq(i=0,i=0..n)]);
 II := `list_elements/threads/subdiv`(p,n)(theta);
 for i in II do
  x[i[1]] := x[i[1]] + 1/`mu/threads/subdiv`(p,n)(theta)(i);
 od:
 return [seq(x[i],i=0..n)];
end:

######################################################################
# F(p,n) is the set of vertices in the (p+1)-fold barycentric
# subdivision of the n-simplex

`is_element/FF/subdiv` := (p::nonnegint,n::nonnegint) -> proc(alpha_theta)
 local alpha,theta,m;

 if not(type(alpha_theta,list) and nops(alpha_theta) = 2) then
  return false;
 fi;

 alpha,theta := op(alpha_theta);

 if not(type(alpha,list(nonnegint)) and nops(alpha) > 0) then
  return false;
 fi;

 m := nops(alpha) - 1;

 if not(`is_element/simplicial_mono_alt`(m,n)(alpha)) then
  return false;
 fi;

 if not(`is_element/EE/subdiv`(p,m)(theta)) then
  return false;
 fi;

 return true; 
end:

`list_elements/FF/subdiv` := proc(p,n)
 local L,N,m,alpha,theta;
 
 L := NULL:
 N := [seq(i,i=0..n)];
 for alpha in combinat[powerset](N) do
  m := nops(alpha) - 1;
  if m >= 0 then
   L := L,seq([alpha,theta],theta in `list_elements/EE/subdiv`(p,m));
  fi;
 od:

 return [L];
end:

`random_element/FF/subdiv` := (p,n) -> proc()
 local d,m,alpha,theta;
 
 d := rand(1..n)();
 alpha := `random_subset_of`({seq(i,i=0..n)},d);
 alpha := sort([op(alpha)]);
 m := nops(alpha) - 1;
 theta := `random_element/EE/subdiv`(p,m)();
 return [alpha,theta];
end:

# This function is not quite right.  It seems to find a correct morphism
# when one exists, but it claims that morphisms exist when that is not the case.

`find_morphism/FF/subdiv` := (p::nonnegint,n::nonnegint) -> proc(alpha_theta0,alpha_theta1)
 local alpha0,alpha1,theta0,theta1,m0,m1,k0,k1,f,h,i,j,u,v,xi,V,W,G,H;

 alpha0,theta0 := op(alpha_theta0);
 alpha1,theta1 := op(alpha_theta1);
 m0 := nops(alpha0) - 1;
 m1 := nops(alpha1) - 1;
 k0 := `degrees/EE/subdiv`(p,m0)(theta0);
 k1 := `degrees/EE/subdiv`(p,m1)(theta1);

 f := table([seq(i=FAIL,i=0..n)]);
 for i from 0 to m1 do f[alpha1[i+1]] := i; od;
 xi := [[seq(f[alpha0[i+1]],i=0..m0)]];
 if member(FAIL,xi[1]) then return FAIL; fi;
 for j from 0 to p-1 do
  V := {seq(w,w=0..k0[j+1])};
  W := {seq(w,w=0..k0[j+1+1])};
  G := [seq(select(v -> theta0[j+1][v+1] <= w,V),w in W)];
  H := map(A -> map(v -> theta1[j+1][xi[j+1][v+1]+1],A),G);
  h := map(max,H);
  if h <> sort([op({op(h)})]) then
   return false;
  fi;
  xi := [op(xi),h];
 od;

 return xi;
end:

`is_leq/FF/subdiv` := (p::nonnegint,n::nonnegint) -> proc(alpha_theta0,alpha_theta1)
 evalb(`find_morphism/FF/subdiv`(p,n)(alpha_theta0,alpha_theta1) <> FAIL);
end:

`xi/FF/subdiv` := (p::nonnegint,n::nonnegint) -> proc(alpha_theta)
 local alpha,theta,i,m,x,y,yt;
 
 alpha,theta := op(alpha_theta);
 m := nops(alpha) - 1;
 x := `xi/EE/subdiv`(p,m)(theta);
 yt := table([seq(i=0,i=0..n)]);
 for i from 0 to m do
  yt[alpha[i+1]] := x[i+1];
 od:
 y := [seq(yt[i],i=0..n)];
 return y;
end:

# Every vertex of the (p+1)-fold subdivision is the barycentre of
# a d-simplex of the p-fold subdivision for some d.  This function
# returns d.

`rank/FF/subdiv` := (p::nonnegint,n::nonnegint) -> proc(alpha_theta)
 local alpha,theta,m;
 
 alpha,theta := op(alpha_theta);
 m := nops(alpha) - 1;
 
 if p = 0 then
  return m;
 else
  return max(op(theta[p]));
 fi;
end:

######################################################################
# Here zeta is a strictly increasing map [j] -> [k] and theta is an
# unordered surjective map [m] -> [k].  The function returns a triple
# [n,beta,phi] where beta : [n] -> [m] is strictly increasing and
# phi : [n] -> [j] is surjective.  In an appropriate context we will
# have alpha^*([x,theta]) = [beta^*(x),phi].

`rewrite/epi/subdiv` := proc(zeta,theta)
 local i,j,m,J,M,k1,N,n,xi,phi;
 
 j := nops(zeta) - 1;
 m := nops(theta) - 1;
 J := {seq(j0,j0=0..j)};
 M := {seq(m0,m0=0..m)};
 
 k1 := op(-1,zeta);
 N := select(m0 -> theta[m0+1] <= k1,M);
 n := nops(N) - 1;
 xi := sort([op(N)]);
 phi := NULL;
 
 for i from 0 to n do
  phi := phi,min(select(j0 -> zeta[j0+1] >= theta[xi[i+1]+1],J));
 od:
 phi := [phi];

 return [n,xi,phi];
end:

`rewrite/FF/subdiv` := (p,n) -> (zeta) -> proc(alpha_theta)
 local alpha,theta,k0,m,xi,phi,alpha1,theta1;
 alpha,theta := op(alpha_theta);
 
 if p = 0 then
  k0 := nops(zeta) - 1;
  return [[seq(alpha[zeta[i+1]+1],i=0..k0)],[]];
 else 
  k0 := nops(zeta) - 1;
  m,xi,phi := op(`rewrite/epi/subdiv`(zeta,theta[p]));
  alpha1,theta1 := op(`rewrite/FF/subdiv`(p-1,n)(xi)([alpha,[op(1..-2,theta)]]));
  return [alpha1,[op(theta1),phi]];
 fi;
end:

`rewrite_aux/FF/subdiv` := (p,n) -> (zeta) -> proc(alpha_theta)
 local alpha,theta,k0,m,xi,phi,xi1,alpha1,theta1;
 alpha,theta := op(alpha_theta);
 
 if p = 0 then
  k0 := nops(zeta) - 1;
  return [[zeta],[seq(alpha[zeta[i+1]+1],i=0..k0)],[]];
 else 
  k0 := nops(zeta) - 1;
  m,xi,phi := op(`rewrite/epi/subdiv`(zeta,theta[p]));
  xi1,alpha1,theta1 := op(`rewrite_aux/FF/subdiv`(p-1,n)(xi)([alpha,[op(1..-2,theta)]]));
  return [[op(xi1),zeta],alpha1,[op(theta1),phi]];
 fi;
end:

`vertices/FF/subdiv` := (p,n) -> proc(alpha_theta)
 local r;
 r := `rank/FF/subdiv`(p,n)(alpha_theta);
 return [seq(`rewrite/FF/subdiv`(p,n)([i])(alpha_theta),i=0..r)];
end:

