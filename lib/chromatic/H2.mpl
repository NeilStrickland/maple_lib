#@ Not autoload

with(LinearAlgebra):

p := 2;
adams_n_max := 5;
adams_s_max := 20;

unprotect('t');
unassign('t');

xi[0] := 1;

protect('t');

HH_vars := plex(seq(xi[i],i=1..adams_n_max));

# The cobar complex involves variables xi[n,s] corresponding to the copy of
# xi[n] in the s'th tensor factor.  We use the ordering with
# xi[1,1] >> xi[2,1] >> xi[3,1] >> ... >> xi[1,2] >> xi[2,2] >> xi[3,2] >> ...
# so the variables from each tensor factor dominate those from the next tensor
# factor.  It is not clear whether this is the best choice.
H_cobar_vars :=
 plex(seq(seq(xi[i,j],i=1..adams_n_max),j=1..adams_s_max));

HH_cmp := (a,b) -> TestOrder(a,b,HH_vars):
H_cobar_cmp := (a,b) -> TestOrder(a,b,H_cobar_vars):

H_degree_rule := {
  seq(xi[n] = e^(2^n-1) * xi[n],n=1..adams_n_max),
  seq(seq(xi[n,i] = e^(2^n-1) * xi[n,i],n=1..adams_n_max),i=1..adams_s_max)
}:

H_degree := (u) -> degree(subs(H_degree_rule,u),e);

H_bidegree := proc(u)
 local s,t;
 t := H_degree(u);
 s := adams_s_max;
 while s > 0 and not(has(u,{seq(xi[i,s],i=1..adams_n_max)})) do
  s := s-1;
 od;
 return [s,t];
end:

# Basis for Z[xi[i] : i >= n] in degree d
T_basis := proc(d::integer,n::posint := 1)
 option remember;
 local m,r,i;
 m := 2^n-1;
 r := floor(d/m);
 if d < 0 then
  return [];
 elif d = 0 then
  return [1];
 elif r = 0 then
  return [];
 else
  map(op,[seq(xi[n]^i *~ T_basis(d-m*i,n+1),i=0..r)]);
 fi;
end:

# Basis for Z[v[i] : i >= n] in degree <= d
T_lower_basis := proc(d::integer,n::posint := 1)
 option remember;
 local m,r,i;
 m := 2^n-1;
 r := floor(d/m);
 if d < 0 then
  return [];
 elif r = 0 then
  return [1];
 else
  map(op,[seq(xi[n]^i *~ T_lower_basis(d-m*i,n+1),i=0..r)]);
 fi;
end:

# Basis for the s-fold tensor power of Z[t_1,t_2,...] in degree d
# The copy of xi[i] in the j'th tensor factor is represented by xi[i,j]
T_power_basis := proc(s::nonnegint,d::integer)
 local B,m,R1,R2,u,v;
 if s = 0 then return `if`(d = 0,[1],[]); fi;

 R1 := {seq(xi[n] = xi[n,1],n=1..adams_n_max)};
 R2 := {seq(seq(xi[n,i] = xi[n,i+1],i=1..s-1),n=1..adams_n_max)};
 B := NULL;
 
 for u in subs(R1,T_lower_basis(d)) do
  m := d - H_degree(u);
  for v in subs(R2,T_power_basis(s-1,m)) do
   B := B,(u*v);
  od;
 od;
 return [B];
end:

# Basis for the s-fold tensor power of the augmentation ideal in
# Z[t_1,t_2,...] in degree d
T_reduced_power_basis := proc(s::nonnegint,d::integer)
 local B,m,R1,R2,u,v;
 if s = 0 then return `if`(d = 0,[1],[]); fi;

 R1 := {seq(xi[n] = xi[n,1],n=1..adams_n_max)};
 R2 := {seq(seq(xi[n,i] = xi[n,i+1],i=1..s-1),n=1..adams_n_max)};
 B := NULL;
 
 for u in subs(R1,T_lower_basis(d)) do
  if u <> 1 then 
   m := d - H_degree(u);
   for v in subs(R2,T_reduced_power_basis(s-1,m)) do
    B := B,(u*v);
   od;
  fi;
 od;
 return [B];
end:

H_cobar_basis := (s,d) -> T_reduced_power_basis(s,d);

# Hopf algebroid coproduct on the generators xi[n]
psi_xi := proc(n)
 local a,b;
 option remember;
 if n = 0 then return 1; fi;

 return xi[n,1] + xi[n,2] + add(xi[n-i,1]^(2^i)*xi[i,2],i=1..n-1);
end:

d_H_cobar_rule := proc(s,i)
 local R0,R1,R2,R3;
 if i = 0 then
  R0 := {seq(xi[j]=xi[j,1],j=1..adams_n_max)};
  R1 := {seq(xi[j]=xi[j,2],j=1..adams_n_max)};
  R2 := {seq(seq(xi[j,k]=xi[j,k+1],k=1..s),j=1..adams_n_max)};
  return {op(R1),op(R2)};
 else
  R0 := {seq(xi[j,1]=xi[j,i],j=1..adams_n_max),
         seq(xi[j,2]=xi[j,i+1],j=1..adams_n_max)};
  R1 := {seq(seq(xi[j,k]=xi[j,k+1],k=i+1..s),j=1..adams_n_max)};
  R2 := {seq(xi[j,i] = subs(R0,psi_xi(j)),j=1..adams_n_max)};
  if i = 1 then
   R3 := {seq(xi[j] = modp(expand(subs(R0,psi_xi(j))),2),j=1..adams_n_max)};
  else
   R3 := {seq(xi[j] = xi[j,1],j=1..adams_n_max)};
  fi;
  return {op(R1),op(R2),op(R3)};
 fi;
end:

d_H_cobar := (s) -> (u) ->
 modp(expand(add(subs(d_H_cobar_rule(s,i),u),i=0..s+1)),2);


d_H_cobar_matrix := proc(s,d)
 local B1,B2,cf;
 B1 := H_cobar_basis(s,d);
 B2 := H_cobar_basis(s+1,d);
 cf := proc(u)
  local sol;
  sol := solve({coeffs(u - add(c[i]*B2[i],i=1..nops(B2)),indets(B2))});
  subs(sol,[seq(c[i],i=1..nops(B2))]);
 end;
 Transpose(Matrix(map(cf,map(d_H_cobar(s),B1))));
end:

mu_H_cobar := (s1,s2) -> proc(a,b)
 local i,b0;
 b0 := b;
 for i from 0 to s1-1 do
  b0 := modp(expand(subs(d_H_cobar_rule(s2+i,0),b0)),2);
 od:
 return modp(expand(a * b0),2);
end:

analyse_H_cobar := proc(s::nonnegint,d::integer)
 local i,R,R0,B1,B2,n1,n2,M,L0,P0,x,x1,L,P,Q,nx,LB2,y,HB,HE,T,U,L1,K,Ki;
 global H_cobar_data;
 
 if d + s >= 2*(p^(adams_n_max + 1) - 1) then
  error("adams_n_max is too small");
 fi;

 if s > adams_s_max then
  error("adams_s_max is too small");
 fi;
 
 R := table():

 if s = 0 then
  if d = 0 then
   R["chain_basis"]     := [1];
   R["chain_rank"]      := 1;
   R["cycle_basis"]     := [1];
   R["cycle_rank"]      := 1;
   R["boundary_basis"]  := [];
   R["boundary_rank"]   := 0;
   R["pivot_data"]      := [[1,infinity]];
   R["non_cycle_basis"] := [];
   R["homology_basis"]  := [1];
   R["homology_exponents"] := [infinity];
  else
   R["chain_basis"]     := H_cobar_basis(0,d);
   R["chain_rank"]      := nops(R["chain_basis"]);
   R["cycle_basis"]     := [];
   R["cycle_rank"]      := 0;
   R["boundary_basis"]  := [];
   R["boundary_rank"]   := 0;
   R["pivot_data"]      := [];
   R["non_cycle_basis"] := R["chain_basis"];
   R["homology_basis"]  := [];
   R["homology_exponents"] := [];
  fi;

  H_cobar_data[s,d] := eval(R);
  return eval(R);
 fi;

 if type(H_cobar_data[s-1,d+1],table) then
  R0 := H_cobar_data[s-1,d+1];
  B1 := R0["non_cycle_basis"];
 else
  B1 := H_cobar_basis(s-1,s+d):
 fi;

 B2 := H_cobar_basis(s,s+d):
 n1 := nops(B1);
 n2 := nops(B2);
 R["chain_basis"] := B2;
 R["chain_rank"]  := n2;

 if n2 = 0 then
  R["cycle_basis"]     := [];
  R["cycle_rank"]      := 0;
  R["boundary_basis"]  := [];
  R["boundary_rank"]   := 0;
  R["pivot_data"]      := [];
  R["non_cycle_basis"] := [];
  R["homology_basis"]  := [];
  R["homology_exponents"] := [];
  H_cobar_data[s,d] := eval(R);
  return eval(R);
 fi;
 
 M := Transpose(Matrix(map(coeff_list,map(d_H_cobar(s-1),B1),B2)));
 L0,P0,x := op(Zpl_reduce(Transpose(M),p)):
 L := Transpose(L0):
 P := Transpose(P0):
 nx := nops(x):
 R["cycle_rank"] := nx;
 
 LB2 := convert(L0.Vector(B2),list):
 R["boundary_basis"] := [seq(LB2[i],i=1..nx)];
 R["cycle_basis"]    := [seq(LB2[i]/p^xi[i][2],i=1..nx)];
 R["pivot_data"]     := x;

 y := sort([op({seq(i,i=1..n2)} minus {seq(xi[i][1],i=1..nx)})]);
 R["non_cycle_basis"] := [seq(B2[i],i in y)];
 
 HB := [];
 HE := [];
 
 for i from 1 to nx do
  if xi[i][2] > 0 then
   HB := [op(HB),R["cycle_basis"][i]];
   HE := [op(HE),p^xi[i][2]];
  fi;
 od;

 R["homology_basis"] := HB;
 R["homology_exponents"] := HE;
  
 T := <IdentityMatrix(nx)|Matrix(nx,n1-nx)>;
 U := Matrix(nx,n2):
 for i from 1 to nx do U[i,xi[i][1]] := 1; od:
 L1 := U.L.Transpose(T);
 Q := P.Transpose(T).(1/L1).U;
 K := <SubMatrix(L,1..n2,1..nx)|Matrix(n2,n2-nx)>;
 y := sort([op({seq(i,i=1..n2)} minus {seq(xi[i][1],i=1..nx)})]);
 for i from 1 to n2 - nx do 
  K[y[i],nx+i] := 1;
 od:
 Ki := 1/K;

 H_cobar_data[s,d] := eval(R);
 return eval(R);
end:

save_H2_data := proc()
 local file;
 file := sprintf("%s/H_2.m",data_dir);
 save(adams_n_max,adams_s_max,psi_xi,H_basis,H_lower_basis,file);
end:

load_H2_data := proc(p)
 local file;
 file := sprintf("%s/H_2.m",data_dir,p);
 load(file);
end:

save_H2_cobar_data := proc()
 local file;
 file := sprintf("%s/H_cobar_data_2.m",data_dir);
 save(H_cobar_data,file);
end:

load_H2_cobar_data := proc()
 local file;
 file := sprintf("%s/H_cobar_data_2.m",data_dir);
 load(file);
end:

adams_representative := proc(u)
 local a,b,c,sa,sb,v,i;
 if type(u,integer) then
  return modp(u,2); 
 elif type(u,`+`) then
  return modp(map(adams_representative,u),2);
 elif type(u,`*`) then
  c,v := selectremove(type,u,integer);
  if modp(c,2) = 0 then
   return 0;
  else
   v := sort([op(v)]);
   a := adams_representative(v[1]);
   b := adams_representative(mul(v[i],i=2..nops(v)));
   sa := H_bidegree(a)[1];
   sb := H_bidegree(b)[1];
   return modp(mu_H_cobar(sa,sb)(a,b),2)
  fi;
 elif type(u,`^`) and type(op(2,u),posint) then
  a := adams_representative(op(1,u));
  b := a;
  sa := H_bidegree(a)[1];
  for i from 2 to op(2,u) do
   b := modp(mu_H_cobar(sa,(i-1)*sa)(a,b),2);
  od;
  return b;
 else
  return procname(args);
 fi;
end:

adams_assassin := proc(err)
 local s,t,B0,B1,M0,V0,MV,sol;
 s,t := op(H_bidegree(err));
 B0 := H_cobar_basis(s-1,t);
 B1 := H_cobar_basis(s,t);
 M0 := d_H_cobar_matrix(s-1,t);
 V0 := Vector(coeff_list(err,B1));
 MV := LinearAlgebra[Modular][Mod](2,<M0|V0>,integer[]):
 sol := LinearAlgebra[Modular][LinearSolve](2,MV,1,inplace=false):
 return ([sol][1] . Vector(B0));
end:

adams_representative(h[0]) := xi[1,1];
adams_representative(h[1]) := xi[1,1]^2;
adams_representative(h[2]) := xi[1,1]^4;
adams_representative(h[3]) := xi[1,1]^8;
adams_representative(c[0]) := xi[1,1]^2*xi[1,2]^7*xi[1,3]^2+xi[1,1]^2*xi[1,2]^4*xi[1,3]^2*xi[2,2]-xi[1,2]^4*xi[1,3]^4*xi[2,1]+xi[1,1]^2*xi[1,2]^3*xi[2,3]^2+xi[1,1]^2*xi[1,2]*xi[1,3]^2*xi[2,2]^2+xi[1,1]^2*xi[1,2]*xi[1,3]^2*xi[2,3]^2+xi[1,1]^2*xi[1,3]^2*xi[3,2]+xi[1,1]^2*xi[2,2]*xi[2,3]^2;

adams_relations := [
 [h[0]*h[1],xi[1,1]^3+xi[2,1]],
 [h[0]^2*h[2]+h[1]^3,xi[1,1]^2*xi[1,2]*xi[2,1]+xi[1,1]^2*xi[1,2]*xi[2,2]+xi[2,1]*xi[2,2]],
 [h[1]*h[2],xi[1,1]^6+xi[2,1]^2],
 [h[0]*h[2]^2,xi[1,1]^5*xi[1,2]^4+xi[1,1]^2*xi[1,2]^7+xi[1,1]^2*xi[1,2]^4*xi[2,1]+xi[1,1]^2*xi[1,2]^4*xi[2,2]+xi[1,2]^6*xi[2,1]+xi[1,1]^2*xi[1,2]*xi[2,2]^2+xi[1,1]^2*xi[3,2]+xi[2,1]*xi[2,2]^2],
 [h[0]^4*h[3],xi[1,1]^2*xi[1,2]^5*xi[1,3]^3*xi[1,4]^2+xi[1,1]^2*xi[1,2]^3*xi[1,3]^2*xi[1,4]^5+xi[1,1]^2*xi[1,2]^2*xi[1,3]^5*xi[1,4]^3+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[1,4]^6+xi[1,1]^6*xi[1,2]*xi[1,3]*xi[1,4]*xi[2,1]+xi[1,1]^4*xi[1,2]^3*xi[1,3]^2*xi[2,4]+xi[1,1]^4*xi[1,2]^3*xi[1,3]*xi[1,4]*xi[2,2]+xi[1,1]^4*xi[1,2]^3*xi[1,3]*xi[1,4]*xi[2,3]+xi[1,1]^2*xi[1,2]^5*xi[1,3]*xi[1,4]*xi[2,2]+xi[1,1]^2*xi[1,2]^4*xi[1,3]^2*xi[1,4]*xi[2,3]+xi[1,1]^2*xi[1,2]^4*xi[1,3]*xi[1,4]^2*xi[2,3]+xi[1,1]^2*xi[1,2]^3*xi[1,3]^3*xi[1,4]*xi[2,3]+xi[1,1]^2*xi[1,2]^3*xi[1,3]^3*xi[1,4]*xi[2,4]+xi[1,1]^2*xi[1,2]^3*xi[1,3]^2*xi[1,4]^2*xi[2,2]+xi[1,1]^2*xi[1,2]^3*xi[1,4]^4*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^4*xi[1,4]*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^4*xi[1,4]*xi[2,4]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^3*xi[1,4]^2*xi[2,2]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^3*xi[1,4]^2*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[1,4]^3*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[1,4]^3*xi[2,4]+xi[1,1]^2*xi[1,3]^4*xi[1,4]^3*xi[2,2]+xi[1,1]^2*xi[1,3]^2*xi[1,4]^5*xi[2,2]+xi[1,2]^4*xi[1,3]^3*xi[1,4]^2*xi[2,1]+xi[1,2]^2*xi[1,3]^2*xi[1,4]^5*xi[2,1]+xi[1,1]^4*xi[1,2]*xi[1,4]*xi[2,2]*xi[2,3]+xi[1,1]^4*xi[1,3]*xi[1,4]*xi[2,2]^2+xi[1,1]^2*xi[1,2]^3*xi[1,3]*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,2]^3*xi[1,4]*xi[2,3]^2+xi[1,1]^2*xi[1,2]^3*xi[1,4]*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[2,1]*xi[2,4]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,2]^2*xi[1,3]^2*xi[2,4]^2+xi[1,1]^2*xi[1,2]^2*xi[1,3]*xi[1,4]*xi[2,1]*xi[2,2]+xi[1,1]^2*xi[1,2]^2*xi[1,3]*xi[1,4]*xi[2,1]*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,3]*xi[1,4]*xi[2,2]^2+xi[1,1]^2*xi[1,2]^2*xi[1,3]*xi[1,4]*xi[2,3]^2+xi[1,1]^2*xi[1,2]^2*xi[1,4]^2*xi[2,2]*xi[2,3]+xi[1,1]^2*xi[1,2]^2*xi[1,4]^2*xi[2,3]^2+xi[1,1]^2*xi[1,2]^2*xi[1,4]^2*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,2]*xi[1,3]^2*xi[1,4]*xi[2,2]*xi[2,3]+xi[1,1]^2*xi[1,2]*xi[1,3]^2*xi[1,4]*xi[2,2]*xi[2,4]+xi[1,1]^2*xi[1,2]*xi[1,3]*xi[1,4]^2*xi[2,2]^2+xi[1,1]^2*xi[1,3]^3*xi[1,4]*xi[2,2]^2+xi[1,1]^2*xi[1,3]^3*xi[1,4]*xi[2,2]*xi[2,3]+xi[1,1]^2*xi[1,3]^3*xi[1,4]*xi[2,2]*xi[2,4]+xi[1,1]^2*xi[1,3]^2*xi[1,4]^2*xi[2,2]*xi[2,3]+xi[1,1]^2*xi[1,4]^4*xi[2,2]*xi[2,3]+xi[1,2]^4*xi[1,3]*xi[1,4]*xi[2,1]^2+xi[1,2]^4*xi[1,3]*xi[1,4]*xi[2,1]*xi[2,2]+xi[1,2]^2*xi[1,3]^3*xi[1,4]*xi[2,1]*xi[2,3]+xi[1,2]^2*xi[1,3]^3*xi[1,4]*xi[2,1]*xi[2,4]+xi[1,2]^2*xi[1,3]^2*xi[1,4]^2*xi[2,1]*xi[2,2]+xi[1,2]^2*xi[1,4]^4*xi[2,1]*xi[2,3]+xi[1,1]^2*xi[1,2]*xi[1,3]*xi[1,4]*xi[3,1]+xi[1,1]^2*xi[1,2]*xi[1,3]*xi[1,4]*xi[3,2]+xi[1,1]^2*xi[1,2]*xi[2,2]*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,3]^2*xi[1,4]*xi[3,2]+xi[1,1]^2*xi[1,3]*xi[1,4]^2*xi[3,2]+xi[1,1]^2*xi[1,3]*xi[2,2]*xi[2,3]*xi[2,4]+xi[1,1]^2*xi[1,4]*xi[2,1]*xi[2,2]*xi[2,3]+xi[1,1]^2*xi[1,4]*xi[2,2]^2*xi[2,3]+xi[1,1]^2*xi[1,4]*xi[2,2]*xi[2,3]*xi[2,4]+xi[1,2]^3*xi[1,3]*xi[1,4]*xi[3,1]+xi[1,2]^2*xi[1,3]*xi[2,1]*xi[2,3]*xi[2,4]+xi[1,2]^2*xi[1,4]*xi[2,1]^2*xi[2,3]+xi[1,2]^2*xi[1,4]*xi[2,1]*xi[2,3]^2+xi[1,2]^2*xi[1,4]*xi[2,1]*xi[2,3]*xi[2,4]+xi[1,2]*xi[1,3]^2*xi[2,1]^2*xi[2,4]+xi[1,2]*xi[1,3]*xi[1,4]*xi[2,1]^3+xi[1,2]*xi[1,3]*xi[1,4]*xi[2,1]^2*xi[2,2]+xi[1,2]*xi[1,3]*xi[1,4]*xi[2,1]^2*xi[2,3]+xi[1,3]^2*xi[1,4]*xi[2,1]*xi[2,2]*xi[2,3]+xi[1,3]^2*xi[1,4]*xi[2,1]*xi[2,2]*xi[2,4]+xi[1,3]*xi[1,4]^2*xi[2,1]*xi[2,2]^2+xi[1,2]*xi[1,4]*xi[2,3]*xi[3,1]+xi[1,3]*xi[1,4]*xi[2,1]*xi[3,2]+xi[2,1]*xi[2,2]*xi[2,3]*xi[2,4]],
[h[1]^2*h[3]+h[2]^3,xi[1,1]^4*xi[1,2]^2*xi[2,1]^2+xi[1,1]^4*xi[1,2]^2*xi[2,2]^2+xi[2,1]^2*xi[2,2]^2],
[h[0]*c[0],xi[1,1]^2*xi[1,2]^5*xi[1,3]^2*xi[2,3]+xi[1,1]^2*xi[1,2]^4*xi[1,3]^3*xi[2,3]+xi[1,1]^2*xi[1,2]^4*xi[2,3]^2+xi[1,1]^2*xi[1,2]^3*xi[1,3]*xi[2,2]^2+xi[1,1]^2*xi[1,2]*xi[1,3]^3*xi[2,2]^2+xi[1,1]^2*xi[1,3]^4*xi[2,2]^2+xi[1,2]^4*xi[1,3]^2*xi[2,1]*xi[2,3]+xi[1,1]^2*xi[1,2]*xi[1,3]^2*xi[3,2]+xi[1,1]^2*xi[1,2]*xi[2,2]^2*xi[2,3]+xi[1,1]^2*xi[1,3]^3*xi[3,2]+xi[1,1]^2*xi[1,3]*xi[2,2]^3+xi[1,1]^2*xi[1,3]*xi[2,2]^2*xi[2,3]+xi[1,3]^3*xi[2,1]*xi[2,2]^2+xi[1,3]^2*xi[2,1]*xi[3,2]+xi[2,1]*xi[2,2]^2*xi[2,3]]
]:

`is_admissible/Steenrod2` := proc(u)
 local v;
 
 if type(u,`+`) or type(u,list) or type(u,set) then
  return `and`(op(map(`is_admissible/Steenrod2`,[op(u)])));
 elif type(u,`*`) then
  v := select(type,[op(u)],specfunc(nonnegint,Sq));
  if nops(v) = 0 then
   return true;
  elif nops(v) = 1 then
   return `is_admissible/Steenrod2`(v[1]);
  else
   return FAIL;
  fi;
 elif type(u,specfunc(nonnegint,Sq)) then
  return `and`(true,seq(evalb(op(j,u) >= 2*op(j+1,u)),j=1..nops(u)-1));
 else
  return true;
 fi;
end:

adem_relation := proc(k::nonnegint,j::nonnegint)
 Sq(k,j) + add(modp(binomial(j-m-1,k-2*m),2) * Sq(j+k-m,m),m=0..floor(k/2));
end:

`reduce_Sq` := proc()
 option remember;
 local a,r,m,n,u,v,j,k;

 a := select(i -> i > 0,[args]);
 r := nops(a);
 
 if `is_admissible/Steenrod2`(Sq(op(a))) then
  return Sq(op(a));
 fi;

 n := 1;
 while n < r and a[n] >= 2*a[n+1] do
  n := n+1;
 od:

 u := seq(a[i],i=1..n-1);
 k := a[n];
 j := a[n+1];
 v := seq(a[i],i=n+2..r);
 return
  modp(add(modp(binomial(j-m-1,k-2*m),2) * reduce_Sq(u,j+k-m,m,v),m=0..floor(k/2)),2);
end:

`reduce/Steenrod2` := (u) -> modp(expand(eval(subs(Sq=reduce_Sq,u))),2);

`mu0/Steenrod2` := proc(u,v)
 if type(u,specfunc(nonnegint,Sq)) and type(v,specfunc(nonnegint,Sq)) then
  return reduce_Sq(op(u),op(v));
 else
  return FAIL;
 fi;
end:

`mu/Steenrod2` := apply_linear_assoc_mod(`mu0/Steenrod2`,Sq(),2);