#@ Not autoload

with(LinearAlgebra):

p := 2;
chromatic_n_max := 4;  # NB degree(v[4]) = 30, degree(v[5]) = 62
chromatic_s_max := 20;

unprotect('v','m','t');
unassign('v','m','t');

v[0] := p;
m[0] := 1;
t[0] := 1;

protect('v','m','t');

# On BP_* we use a lexicographic ordering with v[1] >> v[2] >> v[3] >> ... >> 1.
# This seems to be the best order except that we really want to treat v[0]
# as a variable with v[0] >> v[1], so any monomial multiplied by p comes
# after all the bare monomials.  Then the terms p^t * monomial in any
# given degree have order type omega, and the terms after any given term
# span an invariant ideal.

BP_vars   := plex(seq(v[i],i=1..chromatic_n_max));

# On the other hand, it might be better to use some kind of order that treats
# the powers v[n]^(p^m) in a special way.  This might import more information
# from the chromatic spectral sequence into the ordering.  One option would be
# like
# .. v[1]^(p^2) >> v[2]^(p^2) >> .. >> v[1]^p >> v[2]^p >> .. v[1] >> v[2] >> ...


# On BP_*BP we use a lexicographic ordering with
# v[1] >> v[2] >> .... >> t[1] >> t[2] >> ... >> 1
# This privileges the ideal J = (t[1],...,t[k]); note that BP_*BP/J is
# the Hopf algebroid whose Ext calculates \pi_*(T(k)).

# Again, it might be better to use some kind of order that treats
# the powers t[n]^(p^m) in a special way.  This might import more information
# from the May spectral sequence into the ordering.

BPBP_vars := plex(seq(v[i],i=1..chromatic_n_max),seq(t[i],i=1..chromatic_n_max));

# The cobar complex involves variables t[n,s] corresponding to the copy of
# t[n] in the s'th tensor factor.  We use the ordering with
# v[1] >> v[2] >> ... >> t[1,1] >> t[2,1] >> ... >> t[1,2] >> t[2,2] >> ...
# so the variables from each tensor factor dominate those from the next tensor
# factor.  It is not clear whether this is the best choice.
BP_cobar_vars :=
 plex(op(BPBP_vars),seq(seq(t[i,j],i=1..chromatic_n_max),j=1..chromatic_s_max));
 
BP_cmp   := (a,b) -> TestOrder(a,b,BP_vars):
BPBP_cmp := (a,b) -> TestOrder(a,b,BPBP_vars):
BP_cobar_cmp := (a,b) -> TestOrder(a,b,BP_cobar_vars):

BP_degree := (u) -> degree(subs(BP_degree_rule,u),e);

# Basis for Z[v[i] : i >= n] in degree d
BP_basis := proc(d::integer,n::posint := 1)
 option remember;
 local m,r,i;
 m := 2*p^n-2;
 r := floor(d/m);
 if d < 0 or modp(d,2*p-2) <> 0 then
  return [];
 elif d = 0 then
  return [1];
 elif r = 0 then
  return [];
 else
  map(op,[seq(v[n]^i *~ BP_basis(d-m*i,n+1),i=0..r)]);
 fi;
end:

# Basis for Z[m[i] : i >= n] in degree d
HBP_basis := proc(d::integer,n::posint := 1)
 eval(subs(v = m,BP_basis(d,n)));
end:

# Basis for Z[t[i] : i >= n] in degree d
T_basis := proc(d::integer,n::posint := 1)
 eval(subs(v = t,BP_basis(d,n)));
end:

# Basis for Z[v[i] : i >= n] in degree <= d
BP_lower_basis := proc(d::integer,n::posint := 1)
 option remember;
 local m,r,i;
 m := 2*p^n-2;
 r := floor(d/m);
 if d < 0 or modp(d,2*p-2) <> 0 then
  return [];
 elif r = 0 then
  return [1];
 else
  map(op,[seq(v[n]^i *~ BP_lower_basis(d-m*i,n+1),i=0..r)]);
 fi;
end:

# Basis for Z[m[i] : i >= n] in degree d
HBP_lower_basis := proc(d::integer,n::posint := 1)
 eval(subs(v = m,BP_lower_basis(d,n)));
end:

# Basis for Z[t[i] : i >= n] in degree d
T_lower_basis := proc(d::integer,n::posint := 1)
 eval(subs(v = t,BP_lower_basis(d,n)));
end:

# Basis for BP_*BP in degree d
BPBP_basis := proc(d::integer)
 local B,m,u,v;
 B := NULL;
 for u in BP_lower_basis(d) do
  m := d - BP_degree(u);
  for v in T_basis(m) do
   B := B,(u*v);
  od;
 od;
 return [B];
end:

# Basis for the s-fold tensor power of Z[t_1,t_2,...] in degree d
# The copy of t[i] in the j'th tensor factor is represented by t[i,j]
T_power_basis := proc(s::nonnegint,d::integer)
 local B,m,R1,R2,u,v;
 if s = 0 then return `if`(d = 0,[1],[]); fi;

 R1 := {seq(t[n] = t[n,1],n=1..chromatic_n_max)};
 R2 := {seq(seq(t[n,i] = t[n,i+1],i=1..s-1),n=1..chromatic_n_max)};
 B := NULL;
 
 for u in subs(R1,T_lower_basis(d)) do
  m := d - BP_degree(u);
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

 R1 := {seq(t[n] = t[n,1],n=1..chromatic_n_max)};
 R2 := {seq(seq(t[n,i] = t[n,i+1],i=1..s-1),n=1..chromatic_n_max)};
 B := NULL;
 
 for u in subs(R1,T_lower_basis(d)) do
  if u <> 1 then 
   m := d - BP_degree(u);
   for v in subs(R2,T_reduced_power_basis(s-1,m)) do
    B := B,(u*v);
   od;
  fi;
 od;
 return [B];
end:

BP_cobar_basis := (s,d) ->
 [seq(seq(seq(a*b,a in BP_basis(i)),b in T_reduced_power_basis(s,d-i)),i=0..d)];

# Hazewinkel generators in terms of log coefficients
vm := proc(n::nonnegint)
 option remember;
 if n = 0 then
  return p;
 else 
  return expand(p*m[n] - add(m[k]*vm(n-k)^(p^k),k=1..n-1));
 fi;
end:

# Log coefficients in terms of Hazewinkel generators
# This is inefficient; should use Ravenel's formulae instead
mv := proc(n::nonnegint)
 local err;
 option remember;

 if n = 0 then return 1; fi;
 
 err := vm(n) - v[n];
 err := expand(subs({seq(m[i] = mv(i),i=1..n-1)},err));
 
 return rhs(solve(err=0,{m[n]})[1]);
end:

# Right unit map on the log coefficients
eta_m := (k) -> add(m[i] * t[k-i]^(p^i),i=0..k);

# Right unit map on the Hazewinkel generators
eta_v := proc(k::posint,s::nonnegint)
 option remember;
 local u,R;

 if nargs = 1 then
  u := expand(subs({seq(m[i] = eta_m(i),i=1..k)},vm(k)));
  u := expand(subs({seq(m[i] = mv(i),i=1..k)},u));
  return u;
 else
  if s = 0 then
   return v[k];
  elif s = 1 then
   u := expand(subs({seq(m[i] = eta_m(i),i=1..k)},vm(k)));
   u := expand(subs({seq(m[i] = mv(i),i=1..k)},u));
   u := subs({seq(t[i] = t[i,1],i=1..chromatic_n_max)},u);
   return u;
  else
   u := eta_v(k,s-1);
   R := { seq(seq(t[i,j] = t[i,j+1],i=1..chromatic_n_max),j=1..s-1),
          seq(v[i] = eta_v(i,1),i=1..chromatic_n_max) };
   u := subs(R,u);
   return u;
  fi;
 fi;
end:

# Hopf algebroid coproduct on the generators t[n]
psi_t := proc(n)
 local a,b;
 option remember;
 if n = 0 then return 1; fi;

 a := add(add(mv(i)*t[j,1]^(p^i)*t[n-i-j,2]^(p^(i+j)),j=0..n-i),i=0..n);
 b := add(mv(i)*psi_t(n-i)^(p^i),i=1..n);
 a := subs({t[0,1]=1,t[0,2]=1},a);
 b := subs({t[0,1]=1,t[0,2]=1},b);
 return expand(a - b);
end:

d_BP_cobar_rule := proc(s,i)
 local R0,R1,R2,R3;
 if i = 0 then
  R0 := {seq(t[j]=t[j,1],j=1..chromatic_n_max)};
  R1 := {seq(t[j]=t[j,2],j=1..chromatic_n_max)};
  R2 := {seq(seq(t[j,k]=t[j,k+1],k=1..s),j=1..chromatic_n_max)};
  return 
   {seq(v[j] = expand(subs(R0,eta_v(j))),j=1..chromatic_n_max),op(R1),op(R2)};
 else
  R0 := {seq(t[j,1]=t[j,i],j=1..chromatic_n_max),
         seq(t[j,2]=t[j,i+1],j=1..chromatic_n_max),
	 seq(v[j] = eta_v(j,i-1),j=1..chromatic_n_max)};
  R1 := {seq(seq(t[j,k]=t[j,k+1],k=i+1..s),j=1..chromatic_n_max)};
  R2 := {seq(t[j,i] = subs(R0,psi_t(j)),j=1..chromatic_n_max)};
  if i = 1 then
   R3 := {seq(t[j] = expand(subs(R0,psi_t(j))),j=1..chromatic_n_max)};
  else
   R3 := {seq(t[j] = t[j,1],j=1..chromatic_n_max)};
  fi;
  return {op(R1),op(R2),op(R3)};
 fi;
end:

d_BP_cobar := (s) -> (u) ->
 expand(add((-1)^i * subs(d_BP_cobar_rule(s,i),u),i=0..s+1));


d_BP_cobar_matrix := proc(s,d)
 local B1,B2,cf;
 B1 := BP_cobar_basis(s,d);
 B2 := BP_cobar_basis(s+1,d);
 cf := proc(u)
  local sol;
  sol := solve({coeffs(u - add(c[i]*B2[i],i=1..nops(B2)),indets(B2))});
  subs(sol,[seq(c[i],i=1..nops(B2))]);
 end;
 Transpose(Matrix(map(cf,map(d_BP_cobar(s),B1))));
end:

BP_cobar_cycles := proc(s,d)
 local M;
 M := d_BP_cobar_matrix(s,d);
 map(u -> Transpose(Vector(BP_cobar_basis(s,d))) . u,NullSpace(M));
end:

mu_BP_cobar := (s1,s2) -> proc(a,b)
 local i,b0;
 b0 := b;
 for i from 0 to s1-1 do
  b0 := expand(subs(d_BP_cobar_rule(s2+i,0),b0));
 od:
 return expand(a * b0);
end:

analyse_BP := proc(p_,n_)
 global p,chromatic_n_max;

 if nargs > 0 then p := p_; fi;
 if nargs > 1 then chromatic_n_max := n_; fi;

 vm(chromatic_n_max);
 mv(chromatic_n_max);
 eta_v(chromatic_n_max);
 psi_t(chromatic_n_max);
 NULL;
end:

analyse_BP_cobar := proc(s::nonnegint,d::integer)
 local i,R,R0,B1,B2,n1,n2,M,L0,P0,x,x1,L,P,Q,nx,LB2,y,HB,HE,T,U,L1,K,Ki;
 global BP_cobar_data;
 
 if d + s >= 2*(p^(chromatic_n_max + 1) - 1) then
  error("chromatic_n_max is too small");
 fi;

 if s > chromatic_s_max then
  error("chromatic_s_max is too small");
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
   R["chain_basis"]     := BP_cobar_basis(0,d);
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

  BP_cobar_data[s,d] := eval(R);
  return eval(R);
 fi;

 if type(BP_cobar_data[s-1,d+1],table) then
  R0 := BP_cobar_data[s-1,d+1];
  B1 := R0["non_cycle_basis"];
 else
  B1 := BP_cobar_basis(s-1,s+d):
 fi;

 B2 := BP_cobar_basis(s,s+d):
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
  BP_cobar_data[s,d] := eval(R);
  return eval(R);
 fi;
 
 M := Transpose(Matrix(map(coeff_list,map(d_BP_cobar(s-1),B1),B2)));
 L0,P0,x := op(Zpl_reduce(Transpose(M),p)):
 L := Transpose(L0):
 P := Transpose(P0):
 nx := nops(x):
 R["cycle_rank"] := nx;
 
 LB2 := convert(L0.Vector(B2),list):
 R["boundary_basis"] := [seq(LB2[i],i=1..nx)];
 R["cycle_basis"]    := [seq(LB2[i]/p^x[i][2],i=1..nx)];
 R["pivot_data"]     := x;

 y := sort([op({seq(i,i=1..n2)} minus {seq(x[i][1],i=1..nx)})]);
 R["non_cycle_basis"] := [seq(B2[i],i in y)];
 
 HB := [];
 HE := [];
 
 for i from 1 to nx do
  if x[i][2] > 0 then
   HB := [op(HB),R["cycle_basis"][i]];
   HE := [op(HE),p^x[i][2]];
  fi;
 od;

 R["homology_basis"] := HB;
 R["homology_exponents"] := HE;
  
 T := <IdentityMatrix(nx)|Matrix(nx,n1-nx)>;
 U := Matrix(nx,n2):
 for i from 1 to nx do U[i,x[i][1]] := 1; od:
 L1 := U.L.Transpose(T);
 Q := P.Transpose(T).(1/L1).U;
 K := <SubMatrix(L,1..n2,1..nx)|Matrix(n2,n2-nx)>;
 y := sort([op({seq(i,i=1..n2)} minus {seq(x[i][1],i=1..nx)})]);
 for i from 1 to n2 - nx do 
  K[y[i],nx+i] := 1;
 od:
 Ki := 1/K;

 BP_cobar_data[s,d] := eval(R);
 return eval(R);
end:

BP_set_p := proc(p_)
 global p,v,BP_degree_rule,BP_basis,BP_lower_basis,vm,mv,eta_v,psi_t;

 p := p_;
 unprotect('v');
 v[0] := p;
 protect('v');
 
 BP_degree_rule := {
  seq(v[n] = e^(2*(p^n-1)) * v[n],n=1..chromatic_n_max),
  seq(t[n] = e^(2*(p^n-1)) * t[n],n=1..chromatic_n_max),
  seq(seq(t[n,i] = e^(2*(p^n-1)) * t[n,i],n=1..chromatic_n_max),i=1..chromatic_s_max)
 }:

 forget(BP_basis);
 forget(BP_lower_basis);
 forget(vm);
 forget(mv);
 forget(eta_v);
 forget(psi_t);
 NULL;
end:

save_BP_data := proc()
 local file;
 file := sprintf("%s/BP_%d.m",data_dir,p);
 save(p,chromatic_n_max,chromatic_s_max,vm,mv,eta_v,psi_t,BP_basis,BP_lower_basis,file);
end:

load_BP_data := proc(p)
 local file;
 file := sprintf("%s/BP_%d.m",data_dir,p);
 load(file);
end:

save_BP_cobar_data := proc()
 local file;
 file := sprintf("%s/BP_cobar_data_%d.m",data_dir,p);
 save(BP_cobar_data,file);
end:

load_BP_cobar_data := proc(p)
 local file;
 file := sprintf("%s/BP_cobar_data_%d.m",data_dir,p);
 load(file);
end:

