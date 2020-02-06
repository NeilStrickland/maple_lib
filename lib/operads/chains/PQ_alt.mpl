# This file contains code related to the following situation.
# We have P0 in ICP_N(A) restricting to Q0 in ICP_N(B),
# where B = A \ {a}.  We also have Q1 in ICP_N(B) refining Q0.
# We let U denote the poset of elements M in ICP_N(A) such that
# the restriction of M to B is Q1, and M refines P0.
# The claim is that |U| is contractible.

`random_element/PQ` := (N::posint) -> (A::set,a) -> proc()
 local B,P,Q0,Q;
 B := A minus {a};
 P := `random_element/ICP`(N)(A)():
 Q0 := `res/ICP`(N)(A,B)(P):
 Q := NULL:
 while Q = NULL or not(`is_leq/ICP`(N)(B)(Q0,Q)) do
  Q := `random_element/ICP`(N)(B)():
 od:
 return [P,Q];
end: 

######################################################################

`analyse/PQ` := (N::posint) -> (A::set,a) -> proc(PQ)
 local B,P,Q,T,Pt,Qt,Pr,Qr,Ps,Qs,F,U,m,sigma,Y,Z,zeta,B0,F0,FR0,U0,UR0,
  i,j,k,b;
 B := A minus {a};
 P,Q := op(PQ);
 T := table():
 T["N"] := N;
 T["A"] := A;
 T["B"] := B;
 T["a"] := a;
 T["P"] := P;
 T["Q"] := Q;
 Pt := `totalise/ICP/ord`(N)(A)(P);
 Qt := `totalise/ICP/ord`(N)(B)(Q);
 T["P_tot"] := Pt;
 T["Q_tot"] := Qt;
 Pr := table():
 Qr := table():
 Ps := table():
 Qs := table():
 for i from 1 to N do
  Pr[i]  := `rank_table/preord`(A)(P[i]);
  Qr[i]  := `rank_table/preord`(B)(Q[i]);
  Ps[i] := `strictify/preord`(A)(P[i]);
  Qs[i] := `strictify/preord`(B)(Q[i]);
 od:
 T["P_rank_table"] := eval(Pr);
 T["Q_rank_table"] := eval(Qr);
 T["P_strict"] := Ps;
 T["Q_strict"] := Qs;
 F := table():
 U := table():
 m := table():
 sigma := table():
 Y := table():
 Z := table():
 zeta := table():
 for b in B do
  F[b] := 
   {seq(seq(`f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([i,e]),e in {-1,1}),i=1..N)};
  U[b] := select(M -> `is_leq/ICP`(N)(A)(P,M),F[b]):
  k := 1;
  while member([a,b],P[k]) and member([b,a],P[k]) do
   k := k+1;
  od:
  m[b] := k;
  if member([a,b],P[k]) then
   sigma[b] := -1;
   Y[b] := select(z -> member([a,z],Ps[k]) and member([z,b],Qs[k]),B);
   Z[b] := {seq(op(select(z -> member([a,z],Ps[k]) and
                               member([z,b],Qs[n]),B)),n = k .. N)};
   if Z[b] = {} then 
    zeta[b] := b;
   else
    i := 1;
    while i < nops(Qt) and not(member(Qt[i],Z[b])) do i := i+1; od;
    zeta[b] := Qt[i];
   fi;
  else
   sigma[b] := +1;
   Y[b] := select(z -> member([z,a],Ps[k]) and member([b,z],Qs[k]),B);
   Z[b] := {seq(op(select(z -> member([z,a],Ps[k]) and
                               member([b,z],Qs[n]),B)),n = k .. N)};
   if Z[b] = {} then 
    zeta[b] := b;
   else
    i := nops(Qt);
    while i > 1 and not(member(Qt[i],Z[b])) do i := i-1; od;
    zeta[b] := Qt[i];
   fi;
  fi;
 od:
 B0 := select(b -> Z[b] = {},B);
 T["B0"] := B0;
 T["F"] := eval(F);
 T["U"] := eval(U);
 T["m"] := eval(m);
 T["sigma"] := eval(sigma);
 T["Y"] := eval(Y);
 T["Z"] := eval(Z);
 T["zeta"] := eval(zeta);
 T["FF"] := {seq(op(F[b]),b in B)};
 T["UU"] := select(M -> `is_leq/ICP`(N)(A)(P,M),T["FF"]);
 T["nF"] := nops(T["FF"]);
 T["nU"] := nops(T["FF"]);
 F0,FR0 := op(`skeleton/partord/from_comparator`(T["FF"])(`is_leq/ICP`(N)(A)));
 U0,UR0 := op(`skeleton/partord/from_comparator`(T["UU"])(`is_leq/ICP`(N)(A)));
 T["FF_skel"] := [F0,FR0];
 T["UU_skel"] := [U0,UR0];
 T["FF_hasse"] := `hasse_diagram/partord`(F0)(FR0);
 T["UU_hasse"] := `hasse_diagram/partord`(U0)(UR0);

 return eval(T):
end:

######################################################################

`describe/PQ` := proc(T)
 cat(`describe/ICP`(T["N"])(T["A"])(T["P"]),"\n",
     `describe/ICP`(T["N"])(T["B"])(T["Q"]));
end:

######################################################################

`check/prop_part_is_sphere/PQ` := proc(T)
 global reason;
 local N,A,B,B0,P,Q,U,m,Y,Z,zeta,sigma,b,c,V;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 P := T["P"];
 Q := T["Q"];
 U := T["U"];
 m := T["m"];
 Y := T["Y"];
 Z := T["Z"];
 zeta  := T["zeta"];
 sigma := T["sigma"];
 
 for b in B do 
  V := 
   {seq(seq(`f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([i,e]),e in {-1,1}),i=1..m[b]-1)};
  if Y[b] = {} then
   V := {op(V),`f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([m[b],sigma[b]])};
  fi;
  if U[b] <> V then
   reason := ["UV",b,U[b],V];
   return false;
  fi;
  if Z[b] <> {} then
   c := zeta[b];
   if Z[b] intersect B0 <> {c} then
    reason := ["ZB",b,c,Z[b],B0];
    return false;
   fi;
   if not(m[c] = m[b] and sigma[c] = sigma[b]) then
    reason := ["m",b,c,m[b],m[c],sigma[b],sigma[c]];
    return false;
   fi;
   if U[b] minus U[c] <> {} then
    reason := ["UU",b,c,U[b],U[c]];
    return false;
   fi;
  fi;
 od;
 return true;
end:

######################################################################

`check/cor_Ub_union/PQ` := proc(T)
 global reason;
 local N,A,B,B0,P,Q,U,UU0,UU1;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 P := T["P"];
 Q := T["Q"];
 U := T["U"];
 
 UU0 := {seq(op(U[b]),b in B0)};
 UU1 := {seq(op(U[b]),b in B)};

 if not(T["UU"] = UU0 and UU0 = UU1) then
  reason := [T["UU"],UU0,UU1];
  return false;
 fi;

 return true;
end:

######################################################################

`check/lem_mk/PQ` := proc(T)
 global reason;
 local N,A,B,B0,P,Qs,m,sigma,k,bc,b,c;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 P := T["P"];
 Qs := T["Q_strict"];
 m := T["m"];
 sigma := T["sigma"];
 
 for k from 1 to N do
  for bc in Qs[k] do
   b,c := op(bc);
   if member(b,B0) and member(c,B0) then
    if m[b] < k or m[c] < k then return false; fi;
    if m[b] = k and sigma[b] <>  1 then return false; fi;
    if m[c] = k and sigma[c] <> -1 then return false; fi;
   fi;
  od;
 od;

 return true;
end:

######################################################################

`check/lem_buc/PQ` := proc(T)
 global reason;
 local N,A,B,B0,Qs,Qt,m,sigma,zeta,
  n,n0,I0,ib,ic,b,c,k,ju,u;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 Qs := T["Q_strict"];
 Qt := T["Q_tot"];
 m := T["m"];
 sigma := T["sigma"];
 zeta  := T["zeta"];
 
 n := nops(B);
 I0 := select(i -> member(Qt[i],B0),[seq(i,i=1..n)]);
 n0 := nops(I0);

 for ib from 1 to n0-1 do
  ic := ib+1;
  b := Qt[I0[ib]];
  c := Qt[I0[ic]];
  k := 1;
  while k < N and not(member([b,c],Qs[k])) do k := k+1; od;

  for ju from I0[ib]+1 to I0[ic]-1 do
   u := Qt[ju];
   if sigma[u] = -1 then
    if zeta[u] <> b then
     return false;
    fi;
    if not member([u,c],Qs[k]) then
     return false;
    fi;
    if not (m[b] > k) then
     return false;
    fi;
   else
    if zeta[u] <> c then
     return false;
    fi;
    if not member([b,u],Qs[k]) then
     return false;
    fi;
    if not (m[c] > k) then
     return false;
    fi;
   fi;
  od;
 od;
 return true;
end:

######################################################################

`check/lem_buvc/PQ` := proc(T)
 global reason;
 local N,A,B,B0,Qs,Qt,m,sigma,zeta,
  n,n0,I0,ib,ic,b,c,k,ju,u,jv,v;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 Qs := T["Q_strict"];
 Qt := T["Q_tot"];
 m := T["m"];
 sigma := T["sigma"];
 zeta  := T["zeta"];
 
 n := nops(B);
 I0 := select(i -> member(Qt[i],B0),[seq(i,i=1..n)]);
 n0 := nops(I0);

 for ib from 1 to n0-1 do
  ic := ib+1;
  b := Qt[I0[ib]];
  c := Qt[I0[ic]];
  k := 1;
  while k < N and not(member([b,c],Qs[k])) do k := k+1; od;

  for ju from I0[ib] to I0[ic]-1 do
   for jv from ju+1 to I0[ic] do 
    u := Qt[ju];
    v := Qt[jv];
    if sigma[u] = b and sigma[v] = c then
     if not(member([u,v],Qs[k])) then
      return false;
     fi;
     if not(k <= m[b] and k <= m[c]) then
      return false;
     fi;
     if m[b] = k and u <> b then 
      return false;
     fi;
     if m[c] = k and v <> c then 
      return false;
     fi;
    fi;
   od;
  od;
 od;
 return true;
end:

######################################################################

`check/prop_U_step/PQ` := proc(T)
 global reason;
 local N,A,B,B0,Qs,Qt,U,
  n,n0,I0,ib,ic,b,c,r,V,V0,V1,M0;

 N := T["N"];
 A := T["A"];
 B := T["B"];
 B0 := T["B0"];
 Qs := T["Q_strict"];
 Qt := T["Q_tot"];
 U := T["U"];
 
 n := nops(B);
 I0 := select(i -> member(Qt[i],B0),[seq(i,i=1..n)]);
 n0 := nops(I0);

 for ib from 1 to n0-1 do
  ic := ib+1;
  b := Qt[I0[ib]];
  c := Qt[I0[ic]];
  V := U[b] intersect U[c];
  r := min(op(map(`rank/ICP`(N)(A),V)));
  V0 := select(M -> `rank/ICP`(N)(A)(M) = r,V);
  if nops(V0) <> 1 then return false; fi;
  M0 := V0[1];
  V1 := remove(M -> `is_leq/ICP`(N)(A)(M0,M),V);
  if V1 <> {} then return false; fi;
 od;
 return true;
end:


