# Let E be the surjection operad, as explained by Berger and Fresse
# following McClure.  We represent a basis element of E(A) by
# expressions S(...), where the arguments are elements of A,
# each element appears at least once, and no two adjacent elements
# are the same.

`is_element/surjections` := (A::set) -> proc(x)
 global reason;
 local i,y,z;

 if x = 0 then return true; fi;
 
 if type(x,`+`) then
  return `and`(op(map(`is_element/surjections`(A),[op(x)])));
 fi;

 if type(x,`*`) then
  y,z := selectremove(type,[op(x)],integer);
  return (nops(z) = 1 and `is_element/surjections`(A)(z[1]));
 fi;
 
 if not type(x,specfunc(S)) then return false; fi;
 if {op(x)} <> A then return false; fi;

 for i from 1 to nops(x) - 1 do
  if x[i] = x[i+1] then return false; fi;
 od;

 return true;
end:

`is_equal/surjections` := (A::set) -> (x0,x1) -> evalb(expand(x0 - x1) = 0);

`is_equal_unsigned/surjections` := (A::set) -> (x0,x1) -> evalb(modp(expand(x0 - x1),2) = 0);

`random_basis_element/surjections` := (A) -> proc(m_)
 local n,m,i,x,ok;

 n := nops(A);

 if n = 0 then return FAIL; fi;

 if n = 1 then 
  if nargs = 0 or m_ = 1 then
   return S(op(A));
  else
   return FAIL;
  fi;
 fi;
 
 if nargs > 0 then
  m := m_;
 else 
  m := rand(0..5)();
 end:

 ok := false;
 while not(ok) do 
  x := [op(A),seq(random_element_of(A),i=1..m)];
  x := combinat[randperm](x);
  ok := true;
  for i from 1 to n + m - 1 do
   if x[i] = x[i+1] then
    ok := false;
    break;
   fi;
  od;
 od;
 x := S(op(x));
 return x;
end:

`random_element/surjections` := (A) -> proc(coeff_range_,num_terms_)
 local coeff_range,num_terms;

 coeff_range := -3..3;
 num_terms := 5;
 if nargs > 0 then coeff_range := args[1]; fi;
 if nargs > 1 then num_terms := args[2]; fi;
 
 add(rand(coeff_range)() * `random_basis_element/surjections`(A)(),i=1..num_terms);
end:

# Let u be a basis element of E(A), of length n say.  A gap means
# a pair (i,i+1) with 1 <= i < i+1 <= n.  The gap is bound if
# u[i] = u[j] for some j > i.  Here we represent a bound gap
# (i,i+1) by its initial index i.  The following function
# returns the ordered list of bound gaps.

`bound_gaps/surjections` := (A) -> proc(u)
 local G,N,M,a;
 G := NULL;
 N := [seq(i,i=1..nops(u))];
 for a in A do 
  M := select(i -> op(i,u) = a,N);
  G := G,op(1..-2,M);
 od:
 G := sort([G]);
 return(G);
end:

# Auxiliary function feeding into `diff/surjections`

`diff0/surjections` := (A::set) -> proc(x)
 local i,j,m,y,z,s,ss,t,l,r;
 
 i := [op(x)];
 m := nops(i);
 
 y := 0;
 s := 1;
 ss := table();
 
 for j from 1 to m do
  l := [op(1..j-1,i)];
  r := [op(j+1..m,i)];
  if member(i[j],r) then
   t := s;
   ss[i[j]] := t;
   s := -s;
  elif member(i[j],l) then
   t := -ss[i[j]];
   ss[i[j]] := t;
  else
   t := 0;
  fi;
  if 1 < j and j < m and op(j-1,i) = op(j + 1,i) then
   t := 0;
  fi;
  y := y + t * S(op(1..j-1,i),op(j+1..m,i));
 od:
end:

# Differential on the surjection chain complex

`diff/surjections` := (A::set) -> apply_linear(`diff0/surjections`(A));

# Auxilary function feeding into `deg/surjections`
`deg0/surjections` := (A) -> (u) -> nops(u) - nops(A);

# Degree function for the surjection chain complex.
`deg/surjections` := (A) -> apply_deg(`deg0/surjections`(A));

`reflect/surjections` := (A) -> proc(u)
 local c,v;
 
 if type(u,`+`) then
  return map(`reflect/surjections`(A),u);
 fi;

 c,v := op(coeff_split(u));

 if not(type(v,specfunc(S))) then return FAIL; fi;

 return (-1)^(nops(v) - nops(A)) * u;
end:

# This is the circle product for the operad structure.
# It is assumed that B is a subset of A and u is in E(A/B) and v is in E(B),
# where A/B is implemented as A \ B u {B}.

`o0/surjections` := (A,B) -> proc(u,v)
 local AB,nu,nv,Nu,Nv,M,l,m,JJ,w,J,k,p,i,j,s;

 AB := A minus B union {B};
 
 nu := nops(u);
 nv := nops(v);
 Nu := [seq(i,i=1..nu)];
 Nv := [seq(i,i=1..nv)];
 M := select(i -> op(i,u) = B,Nu);
 m := nops(M);
 JJ := combinat[choose]([seq(i,i=2..nv+m-1)],m-1);
 JJ := map(J -> [1,seq(J[i]-i,i=1..m-1),nv],JJ);

 w := 0;
 for J in JJ do 
  k := NULL;
  l := NULL;
  p := 1;
  for i from 1 to nu do 
   if op(i,u) = B then
    k := k,seq(op(j,v),j=J[p]..J[p+1]);
    l := l,seq([i,j],j=J[p]..J[p+1]);
    p := p+1;
   else
    k := k,op(i,u);
    l := l,[i,0];
   fi;
  od;
  l := [l];
  s := NULL;
  for i in `bound_gaps/surjections`(AB)(u) do
   j := nops(l);
   while j > 1 and l[j][1] <> i do j := j - 1; od;
   s := s,j;
  od;
  for i in `bound_gaps/surjections`(B)(v) do
   j := nops(l);
   while j > 1 and l[j][2] <> i do j := j - 1; od;
   s := s,j;  
  od;
  w := w + sgn([s]) * S(k);
 od:

 return w;
end:

`o/surjections` := (A,B) -> apply_bilinear(`o0/surjections`(A,B));

`gamma0/surjections` := (A::set,B::set) -> (p) -> proc(y,x)
 local F,J,I0,J0,b,L,m,n,S0,s;

 F := fibres(A,B)(p);
 J := [seq(i,i=0..nops(y)-1)];
 I0 := table():
 J0 := table():
 for b in B do 
  I0[b] := [seq(i,i=0..nops(x[b])-1)];
  J0[b] := select(j -> op(j+1,y) = b,J);
 od:
 L := [[]];

 for b in B do
  m := nops(J0[b]) - 1;
  n := nops(I0[b]) - 1;
  S0 := map(`to_grid_path/shuffles`(m,n),`list_elements/shuffles`(m,n));
  S0 := map(s -> [seq(s[i],i=0..n+m)],S0);
  S0 := map(s -> map(ji -> [J0[b][ji[1]+1],ji[2]],s),S0);
  L := [seq(seq([op(l),op(s)],s in S0),l in L)];
 od:
 L := map(sort,L);
 L := map(l -> S(op(map(ji -> op(ji[2]+1,x[op(ji[1]+1,y)]),l))),L);
 return `+`(op(L));
end:

`gamma/surjections` := eval(extend_gamma_linear(`gamma0/surjections`)):

# We now have various functions related to an interesting filtration
# of the surjections operad.

`flip_count/surjections` := (A::set) -> proc(u,s_)
 local r,m,a,b,c,u0,i;
 if nargs > 1 then
  r := `rank_table/ord`(A)(s_);
 else
  r := NULL;
 fi;
 
 m := table():
 for a in A do
  for b in A do
   m[a,b] := 0;
   u0 := select(p -> p = a or p = b,[op(u)]);
   for i from 1 to nops(u0) - 1 do
    if u0[i+1] <> u0[i] then m[a,b] := m[a,b] + 1; fi;
   od;

   if m[a,b] > 0 and r <> NULL then
    c := `if`(r[a] < r[b],a,b);
    if u0[-1] = c then m[a,b] := m[a,b] + 1; fi;
   fi;
  od;
 od;

 return eval(m);
end:

`flip_count_matrix/surjections` := (A::set) -> proc(u,s_)
 local m;
 m := `flip_count/surjections`(A)(args);
 return Matrix([seq([seq(m[a,b],b in A)],a in A)]);
end:


`max_flip_count/surjections` := (A::set) -> proc(u)
 local m,mm,a,b;
 
 m := `flip_count/surjections`(A)(u);

 mm := 0;
 for a in A do
  for b in A do
   mm := max(mm,m[a,b]);
  od;
 od;

 return mm;
end:

`is_cell_member/surjections` := (A::set) -> (ms) -> proc(u)
 local m0,m1,s,r,i,j,a,b,c,u0,k,l,y,z;

 if x = 0 then return true; fi;
 if type(x,`+`) then
  return `and`(seq(`is_cell_member/surjections`(A)(ms)(y),y in x));
 fi;
 if type(x,`*`) then
  y,z := selectremove(type,[op(x)],integer);
  if nops(z) = 1 then
   return `is_cell_member/surjections`(A)(ms)(z[1]);
  else
   return false;
  fi;
 fi;
 
 m0,s := op(ms);
 m1 := `flip_count/surjections`(A)(u,s);

 for a in A do
  for b in A do
   if m1[a,b] > m0[a,b] then return false; fi;
  od;
 od;

 return true;
end:

`filtration0/surjections` := (A::set) -> proc(u)
 local m,m_max,s,rr,k,i,r0,r1,a,b;

 if type(u,integer) then return 0; fi;

 return 1 + `max_flip_count/surjections`(A)(u);
end:

`filtration/surjections` := (A::set) ->
 apply_max_deg(`filtration0/surjections`(A));

`rho0/barratt_eccles/surjections` := (A::set) -> proc(x)
 local rr,d,R,r,y,z,z0,ok,i,m;

 rr := nops(A);
 d := nops(x) - 1;
 R := combinat[choose]([seq(i,i=1..d+rr-1)],d);
 R := map(r -> [0,op(r),d+rr],R);
 R := map(r -> [seq(r[i+1]-r[i],i=1..d+1)],R);
 y := 0;
 for r in R do 
  z := NULL;
  z0 := NULL;
  ok := true;
  for i from 1 to d+1 do
   m := select(j -> not(member(j,[z0])),op(i,x));
   if nops(m) >= r[i] and ([z] = [] or [z][-1] <> m[1]) then
    z := z,op(1..r[i],m);
    z0 := z0,op(1..r[i]-1,m);
   else 
    ok := false;
    break;
   fi;
  od;
  if ok then y := y + S(z); fi;
 od;
 return y;
end:

`rho/barratt_eccles/surjections` := (A::set) -> 
 apply_linear(`rho0/barratt_eccles/surjections`(A));

# We now define a map from the surjections operad to the
# Barratt-Eccles operad.  This is not an operad morphism,
# but it is a section of the map in the opposite direction.

`sigma0/surjections/barratt_eccles` := (A::set) -> proc(x)
 local i,j,k,l,r,t,p,m,d,w,ww;
 
 i := [op(x)];
 m := nops(i);
 d := m - nops(A);

 ww := NULL;

 for k from 0 to d do 
  w := NULL;

  p := 0;
  
  for j from 1 to m do
   l := [op(1..j-1,i)];
   r := [op(j+1..m,i)];
   if member(i[j],r) then
    t := false;
    p := p + 1;
   else
    t := true;
   fi;

   if not(member(i[j],[w])) then
    if t or (p > k) then
     w := w,i[j];
    fi;
   fi;
  od:
  w := [w];
  ww := ww,w;
 od;
 
 return T(ww);
end:

`sigma/surjections/barratt_eccles` := (A::set) -> 
 apply_linear(`sigma0/surjections/barratt_eccles`(A));

# The cut operation construction gives a morphism from the surjection
# operad to the Eilenberg-Zilber operad.  Unfortunately the EZ operad
# cannot be represented properly in our framework because each set
# EZ(A) is an infinite product over the natural numbers.  To deal with
# this we insert natural number indices in various places.

`cut_operation0/surjections` := (n::nonnegint) -> (A::set) -> proc(x)
 local A0,m,d,N,J,p,q,r,j,c,t,a,is_degen;

 A0 := sort([op(A)]);
 m := nops(A);
 d := nops(x) - m;
 N := [seq(i,i=0..n)];
 J := [[0]];
 for p from 1 to m + d - 1 do 
  J := [seq(seq([op(j),q],q=j[-1]..n),j in J)];
 od:
 J := map(j -> [op(j),n],J);

 c := 0;

 for j in J do 
  t := table():
  for a in A0 do t[a] := []: od:
  for p from 1 to m+d do 
   a := op(p,x);
   t[a] := [op(t[a]),seq(r,r=j[p]..j[p+1])];
  od:

  is_degen := false;

  for a in A0 do 
   if nops(t[a]) > nops({op(t[a])}) then 
    is_degen := true;
    break;
   fi;
  od:

  if not(is_degen) then 
   c := c + `detranspose/eilenberg_zilber`(A)(t);
  fi;
 od:

 return c;
end:

`cut_operation1/surjections` := (n::nonnegint) -> (A::set) -> proc(x)
 add(`cut_operation0/surjections`(k)(A)(x),k=0..n);
end:

`cut_operation/surjections` := (n::nonnegint) -> (A::set) ->
 apply_linear(`cut_operation1/surjections`(n)(A));

`multiplicity_table/surjections` := (A::set) -> proc(x)
 local t,a;

 t := table():
 for a in A do t[a] := 0; od:
 for a in [op(x)] do 
  t[a] := t[a] + 1;
 od:
 return eval(t);
end:
`max_multiplicity/surjections` := (A::set) -> proc(x)
 local t,m,a;
 t := `multiplicity_table/surjections`(A)(x);
 m := 0;
 for a in A do m := max(m,t[a]); od;
 return m;
end:
`is_biased/surjections` := (A::set) -> proc(x,a0_)
 local a,a0,t;

 a0 := NULL;
 if nargs > 1 then a0 := a0_; fi;

 t := `multiplicity_table/surjections`(A)(x);

 for a in A do 
  if t[a] > 1 then 
   if a0 = NULL then
    a0 := a;
   else
    if a0 <> a then 
     return false;
    fi;
   fi;
  fi;
 od:

 return true;
end:
`is_strongly_biased/surjections` := (A::set) -> proc(x,a0_)
 local a,a0,t;

 a0 := NULL;
 if nargs > 1 then a0 := a0_; fi;

 t := `multiplicity_table/surjections`(A)(x);

 for a in A do 
  if t[a] > 1 then 
   if a0 = NULL then
    a0 := a;
   else
    if a0 <> a then 
     return false;
    fi;
   fi;
  fi;
 od:
 
 if a0 = NULL or t[a0] <= 1 then return false; fi;

 return true;
end:

