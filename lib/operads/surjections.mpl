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

`diff/surjections` := (A::set) -> apply_linear(`diff0/surjections`(A));

`deg0/surjections` := (A) -> (u) -> nops(u) - nops(A);
`deg/surjections` := (A) -> apply_deg(`deg0/surjections`(A));

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


