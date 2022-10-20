n_max := 6; # Number of generators to use in the dual Steenrod algebra
x_max := 6; # Number of variables for symmetric functions etc

# bar(a,...,z) is the tensor product of a..z over Z/2.
# The code ensures that this behaves in a multininear way.
bar := proc()
 local n,m,i,j,u,a,v,ac,av,x,y;
 n := nargs;
 for i from 1 to n do
  u := seq(args[j],j=1..i-1);
  a := args[i];
  v := seq(args[j],j=i+1..n);
  if type(a,`+`) then
   return map(t -> bar(u,t,v),a);
  elif type(a,integer) and modp(a,2) = 0 then
   return 0;
  elif type(a,`*`) then
   ac,av := selectremove(type,a,rational);
   ac := modp(ac,2);
   if ac <> 1 then
    return ac * bar(u,av,v);
   fi;
  elif type(a,specfunc(bar)) then
   return bar(u,op(a),v);
  fi;
 od;
 return 'procname'(args);
end:

# The next few functions expect an argument like Sq(i,...,j),
# representing a composite like Sq^i ... Sq^j
steenrod_length := proc(u::specfunc(nonnegint,Sq)) nops(u); end:
steenrod_deg    := proc(u::specfunc(nonnegint,Sq)) `+`(op(u)); end:
steenrod_excess := proc(u::specfunc(nonnegint,Sq))
 local i;
 add(op(i,u) - 2*op(i+1,u), i=1..nops(u)-1);
end:

is_admissible := proc(u::specfunc(nonnegint,Sq))
 local m,i;
 m := nops(u);
 for i from 1 to m-1 do
  if op(i,u) < 2*op(i+1,u) then return false; fi;
 od;
 return true;
end:

admissible_basis := proc(n::nonnegint)
 option remember;
 local L,i,v;
 
 if n = 0 then return [Sq()]; fi;
 L := NULL;
 for i from 1 to n do
  for v in admissible_basis(n-i) do
   if i = n or i >= 2 * op(1,v) then
    L := L,Sq(i,op(v));
   fi;
  od;
 od;

 return [L];
end:

# A comparison function for admissible monomials
admissible_lt := proc(u,v)
 local i;
 if steenrod_deg(u) < steenrod_deg(v) then return true;  fi;
 if steenrod_deg(u) > steenrod_deg(v) then return false; fi;

 for i from 1 to min(nops(u),nops(v)) do
  if op(i,u) < op(i,v) then return true; fi;
  if op(i,u) > op(i,v) then return false; fi;
 od:

 if nops(u) > nops(v) then return true; fi;
 return false;
end:

# If A is an admissible monomial of degree d (and thus an element of the
# Steenrod algebra) then mate(A) is an element of the dual Steenrod
# algebra of the same degree.  The dual Steenrod algebra is polynomial
# on generators that we call a[i], of degree 2^i - 1 (for i > 0).
# The element mate(A) is a monomial in these generators.  The standard
# pairing satisfies <A, mate(A)> = 1, and <A,mate(B)> = 0 for A > B.
mate := proc(u::specfunc(nonnegint,Sq))
 local m,i,t;
 
 if not(is_admissible(u)) then return FAIL; fi;

 m := nops(u);
 i := [op(u),0];
 return mul(a[t]^(i[t] - 2 * i[t+1]),t=1..m);
end:

# The comate function is the inverse of the mate function.
comate := proc(v)
 local r,alpha,i,t;
 r := n_max;
 while r > 0 and degree(v,a[r]) = 0 do r := r - 1; od;
 if r = 0 then return Sq(); fi;
 alpha := [seq(degree(v,a[t]),t=1..r)];
 return Sq(seq(add(2^(i-t)*alpha[i],i=t..r),t=1..r));
end;

# adem_rhs(k,j) is the right hand side of the Adem relation for
# Sq^k Sq^j.  This is valid for all k and j even though it is
# typically used only for k < 2 j.
adem_rhs := proc(k::nonnegint,j::nonnegint)
 local m;
 modp(add(binomial(j-m-1,k-2*m) * Sq(j+k-m,m),m=0..floor(k/2)),2);
end:

adem_relation := (k,j) -> modp(Sq(k,j) + adem_rhs(k,j),2);

# adem_reduce(T) returns the representation of T as a sum of
# admissible monomials.  This relies on the auxiliary function
# adem_reduce0(T).
adem_reduce0 := proc(u)
 local v,v0,v1,m,r,i;
 if type(u,list) or type (u,set) or type(u,specfunc(anything,bar)) then
  return(map(adem_reduce0,u));
 elif type (u,`+`) then
  return modp(expand(map(adem_reduce0,u)),2);
 elif type (u,`*`) then
  return modp(expand(map(adem_reduce0,u)),2);
 elif type(u,specfunc(nonnegint,Sq)) then
  v := remove(i -> i=0, [op(u)]);
  m := nops(v);
  if m < 2 then return Sq(op(v)); fi;
  i := 1;
  while i < m and v[i] >= 2 * v[i+1] do 
   i := i + 1;
  od;
  if i = m then return Sq(op(v)); fi;
  r := adem_rhs(v[i],v[i+1]);
  if r = 0 then return 0; fi;
  if type(r,`+`) then r := [op(r)] else r := [r]; fi;
  v0 := op(1..i-1,v);
  v1 := op(i+2..-1,v);
  r := map(w -> Sq(v0,op(w),v1),r);
  return modp(`+`(op(r)),2);
 else
  return modp(u,2);
 fi;
end:

adem_reduce := proc(u)
 local v,w;
 v := u;
 w := adem_reduce0(u);
 while w <> v do 
  v := w;
  w := adem_reduce0(v);
 od;
 return w;
end:

# bullett_macdonald_series(n,s,t) is a polynomial in variables s and t
# whose coefficients are products of the form Sq^i Sq^j.  It is known
# that this polynomial is symmetric in s and t, which encodes some
# relations in the Steenrod algebra.  The function
# bullett_macdonald_relation(i,j) returns a relation obtained in this
# way.  
bullett_macdonald_series := proc(n,s,t)
 local i,j;
 return modp(expand(add(add(
    ((t^2+s*t)^i*s^(2*j) + (s^2+s*t)^i*t^(2*j)) * Sq(i,j),
      j=0..n-i),i=0..n)),2);
end:

bullett_macdonald_term := proc(i::nonnegint,j::nonnegint)
 local k0,k;
 k0 := modp(i,2);
 if modp(j,2) <> k0 then return 0; fi;
 return add(
   modp(binomial((j+k)/2,k),2) * Sq((j+k)/2,(i-k)/2),
   k=k0..min(i,j),2);
end:

bullett_macdonald_relation := proc(i::nonnegint,j::nonnegint)
 modp(bullett_macdonald_term(i,j) + bullett_macdonald_term(j,i),2);
end:

# This is another family of relations in the Steenrod algebra,
# derived from work of Singer
singer_relation := proc(p::nonnegint,q::nonnegint)
 local i;
 if p > 2*q then return 0; fi;

 return add(modp(binomial(p,i),2) * Sq(2*q-i+1,q-p+i+1),
            i = max(0,p-q-1)..p);
end:

# steenrod_mul(A,...,Z) expects its arguments to be linear combinations
# of monomials in Steenrod squares, and it returns their product.
# However, no Adem relations are applied, so the product will typically
# involve inadmissible monomials.
steenrod_mul := proc()
 local u,v;
 if nargs = 0 then 
  return Sq();
 elif nargs = 1 then
  return modp(args[1],2);
 elif nargs > 2 then
  return steenrod_mul(steenrod_mul(args[1],args[2]),args[3..-1]);
 fi;

 u := modp(args[1],2);
 v := modp(args[2],2);
 if type(v,`+`) then
  return modp(expand(map(t -> steenrod_mul(u,t),v)),2);
 fi;
 if type(u,`+`) then
  return modp(expand(map(t -> steenrod_mul(t,v),u)),2);
 fi;

 if type(u,specfunc(nonnegint,Sq)) and type(v,specfunc(nonnegint,Sq)) then
  return Sq(op(u),op(v));
 else
  return u * v;
 fi;
end:

# adem_mul(A,...,Z) expects its arguments to be linear combinations
# of monomials in Steenrod squares, and it returns their product,
# expressed as a linear combination of admissible monomials.
adem_mul := proc() adem_reduce(steenrod_mul(args)); end:

# It is known that the Steenrod algebra is generated by elements of
# the form Sq^(2^i).  The function two_power_Sq(n) returns a
# linear combination of products of such elements, which is equal
# to Sq^n.  The function two_power_reduce(u) returns an element
# of the same type that is equal to u.
two_power_Sq := proc(n::nonnegint)
 option remember;
 local m,p,s,t,rel;

 if n = 0 then return Sq(); fi;

 m := n;
 p := 1;
 while modp(m,2) = 0 do m := m/2; p := 2*p; od;
 if p = n then return Sq(n); fi;

 rel := bullett_macdonald_series(n,s,t);
 rel := coeff(coeff(rel,s,p),t,2*n-p) - Sq(n,0);

 return two_power_reduce(rel);
end:

two_power_reduce := proc(u)
 if type(u,list) or type(u,set)  or type(u,specfunc(anything,bar)) then
  return map(two_power_reduce,u);
 elif type(u,`+`) or type(u,`*`) then
  return modp(expand(map(two_power_reduce,u)),2);
 elif type(u,specfunc(nonnegint,Sq)) then
  return steenrod_mul(op(map(two_power_Sq, [op(u)])));
 fi;
end:

# milnor_Q(n) is the n'th Milnor Bockstein element in the Steenrod algebra.
milnor_Q := proc(n::nonnegint)
 option remember;
 local u,v;

 if n = 0 then 
  return Sq(1);
 else
  u := Sq(2^n);
  v := milnor_Q(n-1);
  return modp(adem_mul(u,v) + adem_mul(v,u),2);
 fi;
end:

# cartan_psi() is the standard coproduct operation on the Steenrod algebra.
# It returns a linear combination of elements of the form bar(v,w), which
# represents the tensor product of v and w.  It does not apply Adem relations
# to the answer.  
cartan_psi := proc(u)
 local v,f,m,i,j,k,x;
 if type(u,list) or type(u,set) then 
  return map(cartan_psi,u);
 elif type(u,`+`) or type(u,`*`) then
  return modp(expand(map(cartan_psi,u)),2);
 elif type(u,specfunc(nonnegint,Sq)) then
  v := [bar(Sq(),Sq())];
  f := (i,j) -> v -> bar(Sq(op(op(1,v)),i),Sq(op(op(2,v)),j));
  for k from 1 to nops(u) do
   m := op(k,u);
   v := [seq(seq(f(i,m-i)(x),x in v),i=0..m)];
  od:
  return `+`(op(v));
 else
  return u;
 fi;
end:

# dual_psi() is the standard coproduct on the dual Steenrod algebra.
# Elements of the tensor square are represented as polynomials in the
# variables aL[i] = a[i] @ 1 and aR[i] = 1 @ a[i].
a[0] := 1;
aL[0] := 1;
aR[0] := 1;

dual_psi := proc(u)
 local i,j;
 return subs({seq(a[i] = add(aL[j] * aR[i-j]^(2^j),j=0..i),i=0..n_max)},u);
end:

# steenrod_pairing(u,v) returns the standard pairing of an element u in
# the Steenrod algebra and an element v in the dual Steenrod algebra.
steenrod_pairing := proc(u,v)
 local m,c,i;

 if u = 0 or v = 0 then return 0; fi;

 if type(u,`+`) then 
  return modp(expand(map(t -> steenrod_pairing(t,v),u)),2);
 fi;
 if type(v,`+`) then 
  return modp(expand(map(t -> steenrod_pairing(u,t),v)),2);
 fi;

 if type(u,specfunc(nonnegint,Sq)) then
  m := nops(u);
  if m = 0 then
   c := v;
   for i from 1 to n_max do c := coeff(c,a[i],0); od;
   return modp(c,2);
  elif m = 1 then
   c := coeff(v,a[1],op(u));
   for i from 2 to n_max do c := coeff(c,a[i],0); od;
   return modp(c,2);
  else
   c := coeff(dual_psi(v),aR[1],op(1,u));
   for i from 2 to n_max do c := coeff(c,aR[i],0); od;
   c := eval(subs(aL = a,c));
   c := steenrod_pairing(Sq(op(2..-1,u)),c);
   return c;
  fi;
 else
  return FAIL;
 fi;
end:

# dickson_fW(n)(t) is the monic Dickson polynomial of degree 2^n
# whose coefficients are symbols W[n,i]
dickson_fW := proc(n)
 local t,i;
 return unapply(add(W[n,i] * t^(2^i),i = 0..n-1) + t^(2^n),t);
end:

# dickson_fW(n)(t) is the monic Dickson polynomial of degree 2^n
# whose coefficients are polynomials in variables x[0],...,x[n-1]
dickson_fx := proc(n)
 option remember;
 local t,g,h,i;
 
 if n = 0 then
  return unapply(t,t);
 else
  g := dickson_fx(n-1)(t);
  h := modp(expand(g * add(coeff(g,t,2^i) * (t^(2^i) + x[n-1]^(2^i)),i=0..n-1)),2);
  return unapply(h,t);
 fi;
end:

dickson_W_deg := (n,i) -> 2^n - 2^i;

# dickson_Wx(n,k) is W[n,k] expressed as a polynomial of degree 2^n - 2^k
# in the variables x[0],...,x[n-1]
dickson_Wx := proc(n,k)
 option remember;
 return coeff(dickson_fx(n)(t),t,2^k);
end:

# mui_Vx(k) is the k'th Mui coefficient, expressed as a polynomial of
# degree 2^k in variables x[0],...,x[k]
mui_Vx := (k) -> dickson_fx(k)(x[k]);

mui_V_deg := (i) -> 2^i;

mui_gV := (k) -> unapply(V[k] * t + t^2,t);

mui_gx := (k) -> unapply(mui_Vx(k) * t + t^2,t);

# dickson_WV(n,k) is W[n,k] expressed as a polynomial in the Mui coefficients
# V[0],...,V[n-1].  The function dickson_WV_alt(n,k) calculates the same
# thing in a different way.
dickson_WV := proc(n,k)
 local L,i,j,t;
 if k > n then return 0; fi;
 
 L := combinat[choose]([seq(j,j=0..n-1)],n-k):
 return add(mul(V[i[t]]^(2^(t-i[t]+k-1)),t=1..n-k),i in L);
end:

dickson_WV_alt := proc(n,k)
 option remember;
 local i;
 
 if k > n or k < 0 then return 0; fi;
 if k = n then return 1; fi;
 if k = 0 then return mul(V[i],i=0..n-1); fi;

 return modp(expand(V[n-1] * dickson_WV(n-1,k) + dickson_WV(n-1,k-1)^2),2); 
end:

TSq_x := proc(n) local t; unapply(x[n] + t * x[n]^2, t); end;

TSq_mui_V := proc(n)
 local t,u,i;
 u := t^(2^n) * V[n]^2 + add(t^(2^n - 2^i) * V[n] * dickson_WV(n,i),i=0..n);
 return unapply(u,t);
end:

TSq_dickson_W := proc(n,k)
 local t,u,i,j;
 u := subs(W[n,n] = 1,
       W[n,k]^2 * t^(2^n - 2^k) +
       add(add(W[n,i]*W[n,j]* t^(2^n+2^k-2^i-2^j),j=k+1..n),i=0..k));
 return unapply(u,t);
end:

dickson_w_deg := (n,k) -> 1 - 2^k;

dickson_wW := proc(n::nonnegint,i::nonnegint)
 if i < n then
  return W[n,i]/W[n,0];
 elif i = n then
  return 1/W[n,0];
 else
  return 0;
 fi;
end:

dickson_Ww := proc(n,i)
 if i = 0 then
  return 1/w[n,n];
 elif i <= n then
  return w[n,i]/w[n,n];
 else
  return 0;
 fi;
end:

dickson_wx := (n,i) -> dickson_Wx(n,i)/dickson_Wx(n,0);

dickson_wv := proc(n,k)
 local L,i,j,t;
 L := combinat[choose]([seq(j,j=0..n-1)],k):
 return add(mul(v[i[t]]^(-2^(k-t)),t=1..k),i in L);
end:

dickson_wv_alt := proc(n,k)
 option remember;
 local u;
 
 if k > n or k < 0 then return 0; fi;
 if k = 0 then return 1; fi;

 u := dickson_wv(n-1,k) + dickson_wv(n-1,k-1)^2/v[n-1];
 u := expand(modp(factor(u),2));
 return u;
end:

dickson_fw := proc(n)
 local i;
 return unapply(t + add(w[n,i] * t^(2^i),i=1..n),t);
end:

mui_v_deg := (i) -> 1;

mui_vV := proc(i)
 local j;
 return V[i] / mul(V[j],j=0..i-1);
end:

mui_Vv := proc(i)
 local j;
 mul(v[j] ^ (2^max(i-j-1,0)),j=0..i);
end:

mui_vx := proc(i)
 local j;
 mui_Vx(i) / mul(mui_Vx(j),j=0..i-1);
end:

mui_gv := proc(i)
 local t;
 return unapply(t + t^2/v[i],t);
end:

######################################################################

check_admissible := proc(m::nonnegint)
 local B,BB,n,i,j,u,v;

 B := admissible_basis(m);
 
 _ASSERT(
  `and`(op(map(is_admissible,B))),
  "Admissible moomials are admissible"
 );

 _ASSERT(
  B = sort(B,admissible_lt),
  "Admissible monomials are sorted"
 );

 _ASSERT(
  B = map(comate,map(mate,B)),
  "comate o mate = 1"
 );

 n := nops(B);
 _ASSERT(
  {1,op(map(u -> steenrod_pairing(u,mate(u)),B))} = {1},
  "<A,mate(A)> = 1"
 );

 _ASSERT(
  {0,seq(seq(steenrod_pairing(B[j],mate(B[i])),j=i+1..n),i=1..n)} = {0},
  "<A,mate(B)> = 0 for A > B"
 );

 BB := {seq(seq([u,v],v in B),u in B)};
 BB := select(uv -> steenrod_length(uv[1]) < steenrod_length(uv[2]),BB);
 BB := map(uv -> steenrod_pairing(uv[1],mate(uv[2])), BB);
 _ASSERT(
  BB = {0},
  "<A,mate(B)> = 0 for len(A) < len(B)"
 );

end:

check_adem := proc(m::nonnegint)
 local err,i,u;
 
 err := 
 {0, seq(seq(
      steenrod_pairing(adem_relation(i,m-i),mate(u)),
     i=0..m),u in admissible_basis(m))};

 _ASSERT(err = {0},"Adem relations are compatible with pairing");
end:

check_milnor_Q := proc(m)
 local i,j,Q;

 for i from 0 to m do Q[i] := milnor_Q(i); od;

 _ASSERT(
  {0,seq(adem_mul(Q[i],Q[i]),i=0..m)} = {0},
  "Q_i^2 = 0"
 );

 _ASSERT(
  {0,seq(seq(modp(adem_mul(Q[i],Q[j])+adem_mul(Q[j],Q[i]),2),j=i+1..m),i=0..m)} = {0},
  "Q_i Q_j = Q_j Q_i"
 );

 _ASSERT(
  {0,seq(modp(eval(adem_reduce(cartan_psi(Q[i]) + bar(Sq(),Q[i]) + bar(Q[i],Sq()))),2),i=0..m)} = {0}, 
  "Q_i is primitive"
 );
end:

check_two_power := proc(m)
 local B,i,j,k,err;

 B := [seq(seq(seq(Sq(i,j,k),k=0..m),j=0..m),i=0..m)];

 err := {0,op(map(u -> adem_reduce(u + two_power_reduce(u)),B))};

 _ASSERT(err = {0},"Two-power reduction is consistent");
end:

check_bullett_macdonald := proc(m)
 local s,t,i,j,p,q;
 
 _ASSERT(
  adem_reduce(bullett_macdonald_series(m,s,t)) = 0,
  "Bullett-Macdonald series"
 );

 _ASSERT(
  {0,seq(seq(adem_reduce(bullett_macdonald_relation(i,j)),j=0..20),i=0..20)} = {0},
  "Bullett-Macdonald relations"
 );

 _ASSERT(
  {0,seq(seq(adem_reduce(singer_relation(p,q)),p=0..2*q),q=0..15)} = {0},
  "Singer relations"
 );
end:

check_dickson := proc(m::nonnegint)
 local t,i,k,err;
 
 _ASSERT(
  modp(expand(dickson_fx(m)(t) - add(dickson_Wx(m,i) * t^(2^i),i=0..m)),2) = 0,
  "The Dickson polynomial is additive"
 );

 _ASSERT(
  modp(expand(dickson_Wx(m,0) + mul(mui_Vx(i),i=0..m-1)),2) = 0,
  "W_{m0} = prod_{i<m} V_i"
 );

 _ASSERT(
  {0,seq(modp(expand(
      dickson_Wx(m,k) + mui_Vx(m-1) * dickson_Wx(m-1,k) + dickson_Wx(m-1,k-1)^2
     ),2),k=1..m-1)} = {0},
  "W_{mk} = V_{m-1} W_{m-1,k} + W_{m-1,k-1}^2"
 );

 _ASSERT(
  modp(expand(dickson_fx(m)(t) + mui_gx(m-1)(dickson_fx(m-1)(t))),2) = 0,
  "f_m(t) = g_{m-1}(f_{m-1}(t))"
 );

end:

check_rules := proc(m)
 local Wx_rule, wx_rule, WV_rule, wv_rule,
       Ww_rule, wW_rule, Vx_rule, vx_rule, Vv_rule, vV_rule, i;

 Wx_rule := {seq(W[m,i] = dickson_Wx(m,i),i=0..m+1)}:
 wx_rule := {seq(w[m,i] = dickson_wx(m,i),i=0..m+1)}:
 WV_rule := {seq(W[m,i] = dickson_WV(m,i),i=0..m  )}:
 wv_rule := {seq(w[m,i] = dickson_wv(m,i),i=0..m+1)}:
 Ww_rule := {seq(W[m,i] = dickson_Ww(m,i),i=0..m+1)}:
 wW_rule := {seq(w[m,i] = dickson_wW(m,i),i=0..m+1)}:
 Vx_rule := {seq(V[i] = mui_Vx(i),i=0..m+1)}:
 vx_rule := {seq(v[i] = mui_vx(i),i=0..m+1)}:
 Vv_rule := {seq(V[i] = mui_Vv(i),i=0..m+1)}:
 vV_rule := {seq(v[i] = mui_vV(i),i=0..m+1)}:

 _ASSERT(
  {seq(subs(Vv_rule,subs(vV_rule,v[i])) - v[i],i=0..m-1),
   seq(subs(vV_rule,subs(Vv_rule,V[i])) - V[i],i=0..m-1),
   seq(subs(Ww_rule,subs(wW_rule,w[m,i])) - w[m,i],i=1..m),
   seq(subs(wW_rule,subs(Ww_rule,W[m,i])) - W[m,i],i=0..m-1),
   seq(subs(Ww_rule,subs(wW_rule,w[m,i])) - w[m,i],i=1..m),
   seq(subs(vx_rule,subs(Vv_rule,V[i])) - subs(Vx_rule,V[i]),i=1..m),
   seq(subs(wx_rule,subs(Ww_rule,W[m,i])) - subs(Wx_rule,W[m,i]),i=0..m-1),
   seq(modp(factor(subs(vx_rule,subs(wv_rule,w[m,i])) - subs(wx_rule,w[m,i])),2),i=1..m),
   seq(modp(factor(subs(Vx_rule,subs(WV_rule,W[m,i])) - subs(Wx_rule,W[m,i])),2),i=0..m-1),
   0} = {0},
  "translation rules"
 );
end: