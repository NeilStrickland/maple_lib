# This file contains code related to the following situation.
# We have P0 in ICP_N(A) restricting to Q0 in ICP_N(B),
# where B = A \ {a}.  We also have Q1 in ICP_N(B) refining Q0.
# We let U denote the poset of elements M in ICP_N(A) such that
# the restriction of M to B is Q1, and M refines P0.
# The claim is that |U| is contractible.

`random_element/PQQ` := (N::posint) -> (A::set,a) -> proc()
 local B,P0,Q0,Q1;
 B := A minus {a};
 P0 := `random_element/ICP`(N)(A)():
 Q0 := `res/ICP`(N)(A,B)(P0):
 Q1 := NULL:
 while Q1 = NULL or not(`is_leq/ICP`(N)(B)(Q0,Q1)) do
  Q1 := `random_element/ICP`(N)(B)():
 od:
 return [P0,Q0,Q1];
end: 

######################################################################

`analyse/PQQ` := (N::posint) -> (A::set,a) -> proc(PQQ)
 local B,P0,Q0,Q1,P0r,Q0r,Q1r,L1,n1,T,M,RR,SS,US,PN,PS,U,nU,U0,UR0,
  Q1B,AQ1B,RT,Bm,Bo,Bp,Bmr,Bpr,NB,NU,VV,b,i,j,k,l,beta,kk,ee;
 B := A minus {a};
 P0,Q0,Q1 := op(PQQ);
 T := table():
 T["N"] := N;
 T["A"] := A;
 T["B"] := B;
 T["a"] := a;
 T["P0"] := P0;
 T["Q0"] := Q0;
 T["Q1"] := Q1;
 T["P0_tot"] := `totalise/ICP/ord`(N)(A)(P0);
 T["Q0_tot"] := `totalise/ICP/ord`(N)(B)(Q0);
 T["Q1_tot"] := `totalise/ICP/ord`(N)(B)(Q1);
 P0r := table():
 Q0r := table():
 Q1r := table():
 for i from 1 to N do
  P0r[i] := `rank_table/preord`(A)(P0[i]);
  Q0r[i] := `rank_table/preord`(B)(Q0[i]);
  Q1r[i] := `rank_table/preord`(B)(Q1[i]);
 od:
 T["P0_rank_table"] := eval(P0r);
 T["Q0_rank_table"] := eval(Q0r);
 T["Q1_rank_table"] := eval(Q1r);
 RR := table():
 SS := table():
 US := table():
 for b in B do
  RR[b] := `list_elements/ICP`(N)({a,b}):
  SS[b] := map(`f/fibre_sphere/ICP`(N)(A)(a,b,Q1),RR[b]):
  US[b] := select(M -> `is_leq/ICP`(N)(A)(P0,M),SS[b]):
  PN[b] := evalb(nops(US[b]) > 0);
  PS[b] := evalb(modp(nops(US[b]),2) = 0);
  k := 1;
  while member([a,b],P0[k]) and member([b,a],P0[k]) do
   k := k+1;
  od:
  kk[b] := k;
  ee[b] := `if`(member([a,b],P0[k]),-1,+1);
 od:
 T["fibre_sphere"] := eval(SS);
 T["upper_fibre_part"] := eval(US);
 T["part_is_empty"] := eval(PE);
 T["part_is_sphere"] := eval(PS);
 T["P0_split_stage"] := eval(kk);
 T["P0_split_direction"] := eval(ee);
 T["fibre"] := {seq(op(SS[b]),b in B)};
 U := {seq(op(US[b]),b in B)};
 nU := nops(U);
 U0,UR0 := op(`skeleton/partord/from_comparator`(U)(`is_leq/ICP`(N)(A))); 
 T["upper_fibre"] := U;
 T["U0"] := U0;
 T["upper_fibre_size"] := nU;
 T["upper_fibre_skeleton"] := UR0;
 T["upper_fibre_hasse_diagram"] := 
  `hasse_diagram/partord`(U0)(UR0);
 L1 := T["Q1_tot"];
 n1 := nops(L1);
 T["part_list"] := [seq(US[L1[i]],i=1..n1)];
 T["part_is_nonempty_list"] := [seq(PN[L1[i]],i=1..n1)];
 T["part_is_sphere_list"] := [seq(PS[L1[i]],i=1..n1)];
 T["left_nested_list"] :=
  [FAIL,seq(evalb({op(US[L1[i]])} minus {op(US[L1[i-1]])} = {}),i=2..n1)];
 T["right_nested_list"] :=
  [seq(evalb({op(US[L1[i]])} minus {op(US[L1[i+1]])} = {}),i=1..n1-1),FAIL];
 T["part_skeleton"] := [
  seq(select(i -> member(U[i],US[L1[j]]),U0),j=1..n1)
 ];
 Q1B := table():
 AQ1B := table():
 RT := table():
 Bm := table():
 Bo := table():
 Bp := table():
 Bmr := table():
 Bpr := table():
 NU  := table():
 for i from 1 to N do
  Q1B[i] := `block_partition/equiv`(B)(Q1[i] union `op/autorel`(B)(Q1[i]));
  AQ1B[i] := select(u -> member([u[1],a],P0[i]) or member([a,u[1]],P0[i]),Q1B[i]);
  for beta in AQ1B[i] do
   RT[i,beta] := `rank_table/preord`(beta)(Q1[i]);
   NB[i,beta] := max(0,seq(RT[i,beta][b]+1,b in beta));
   Bm[i,beta] := select(b -> not(member([a,b],P0[i])),beta);
   Bo[i,beta] := select(b -> member([a,b],P0[i]) and member([b,a],P0[i]),beta);
   Bp[i,beta] := select(b -> not(member([b,a],P0[i])),beta);
   Bmr[i,beta] := max(0,seq(RT[i,beta][b]+1,b in Bm[i,beta]));
   Bpr[i,beta] := min(NB[i,beta],seq(RT[i,beta][b],b in Bp[i,beta]));
   NU[i,beta] := Bpr[i,beta] - Bmr[i,beta] + 1;
   VV[i,beta] := {seq([i,beta,l-0.5],l=Bmr[i,beta]..Bpr[i,beta])};
  od:
 od:
 Q1B[N+1] := {seq({b},b in B)};
 AQ1B[N+1] := {};
 T["Q1_comparability_blocks"] := eval(Q1B):
 T["admissible_blocks"] := eval(AQ1B);
 T["admissible_tree"] := [seq(seq([i,beta],beta in AQ1B[i]),i=1..N)];
 T["Q1_rank_table"] := eval(RT);
 T["lower_set"]  := eval(Bm);
 T["middle_set"] := eval(Bo);
 T["upper_set"]  := eval(Bp);
 T["lower_rank"] := eval(Bmr);
 T["upper_rank"] := eval(Bpr);
 T["block_quotient_size"] := eval(NB);
 T["num_U"]      := eval(NU);
 T["V"] := {seq(seq(op(VV[i,beta]),beta in AQ1B[i]),i=1..N)};
 return eval(T):
end:

######################################################################

`f/PQQ/U/V` := (T) -> proc(M)
 local a,b,j,k,beta,beta0,gamma,rt,r;
 k := 1:
 beta := T["B"]:
 a := T["a"]:
 for j from 2 to T["N"] do 
  beta0 := select(b -> member([a,b],M[j]) or member([b,a],M[j]),beta);
  if beta0 <> {} then
   beta := beta0;
   k := j;
  else
   break;
  fi;
 od:
 gamma := select(b -> not(member([a,b],M[k])),beta);
 rt := eval(T["Q1_rank_table"][k,beta]):
 r := max(-1,seq(rt[b],b in gamma)) + 0.5;
 return [k,beta,r];
end:

######################################################################

`g/PQQ/V/U` := (T) -> proc(x)
 local i,k,N,a,b,B,MT,QQ,MM,M,beta,r,b0,L,U,rt;
 k,beta,r := op(x);
 N := T["N"];
 a := T["a"];
 B := T["B"];
 MT := table():
 for i from 1 to N do
  QQ := T["Q1"][i];
  MM := QQ union {[a,a]};
  if i < k then
   b0 := beta[1];
   L := select(b -> member([b,b0],QQ),B);
   U := select(b -> member([b0,b],QQ),B);
   MM := {op(MM),seq([b,a],b in L),seq([a,b],b in U)};
  elif i = k then
   rt := T["Q1_rank_table"][k,beta];
   L := select(b -> rt[b] < r,beta);
   U := select(b -> rt[b] > r,beta);
   MM := {op(MM),seq([b,a],b in L),seq([a,b],b in U)};
  fi;
  MT[i] := MM; 
 od:
 M := [seq(MT[i],i=1..N)];
 return M;
end:

######################################################################

`is_leq/PQQ/V` := (T) -> proc(x0,x1)
 local k0,k1,beta0,beta1,r0,r1,r2,b0;
 k0,beta0,r0 := op(x0);
 k1,beta1,r1 := op(x1);
 if k0 < k1 then return false; fi;
 if k0 = k1 then
  return evalb(beta0 = beta1 and r0 = r1);
 fi;
 b0 := beta0[1];
 if not(member(b0,beta1)) then return false; fi;
 r2 := T["Q1_rank_table"][k1,beta1][b0];
 if not(r1 = r2 - 0.5 or r1 = r2 + 0.5) then
  return false;
 fi;
 return true;
end:

######################################################################

`rho/PQQ` := (T) -> (j,e) -> proc(x)
 local k,beta,gamma,beta1,b0,QQ,rt,r1;
 k,beta,gamma := op(x);
 if j >= k then return FAIL; fi;
 b0 := beta[1];
 QQ := T["Q1"][j];
 beta1 := select(b -> member([b,b0],QQ) or member([b0,b],QQ),T["B"]);
 rt := T["Q1_rank_table"][j,beta1];
 r1 := rt[beta[1]] + 0.5 * e;
 return [j,beta1,r1];
end:

######################################################################

`describe/PQQ` := proc(T)
 cat(`describe/ICP`(T["N"])(T["A"])(T["P0"]),"\n",
     `describe/ICP`(T["N"])(T["B"])(T["Q0"]),"\n",
     `describe/ICP`(T["N"])(T["B"])(T["Q1"]),"\n");
end:

######################################################################

`check_UV/PQQ` := proc(T)
 local N,A,U,V,ff,gg,M,M0,M1,x,x0,x1,cU,cV;
 N := T["N"];
 A := T["A"];
 U := T["upper_fibre"]:
 V := T["V"]:
 ff := table():
 gg := table():
 for M in U do 
  x := `f/PQQ/U/V`(T)(M);
  if not(member(x,V)) then return false; fi;
  M1 := `g/PQQ/V/U`(T)(x);
  if M <> M1 then return false; fi;
  ff[M] := x;
 od:
 for x in V do 
  M := `g/PQQ/V/U`(T)(x);
  if not(member(M,U)) then return false; fi;
  x1 := `f/PQQ/U/V`(T)(M);
  if x <> x1 then return false; fi;
  gg[x] := M;
 od:
 for x0 in V do
  for x1 in V do
   M0 := gg[x0];
   M1 := gg[x1];
   cU := `is_leq/ICP`(N)(A)(M0,M1);
   cV := `is_leq/PQQ/V`(T)(x0,x1);
   if cU <> cV then return false; fi;
  od;
 od;
 return true;
end:

######################################################################

`check_rho/PQQ` := proc(T)
 global reason;
 local VV,i,j,k,x,y,z,C,y1,y2,y3,y4,y5,y6;
 VV := table():
 for k from 1 to T["N"] do 
  VV[k] := select(x -> x[1] = k,T["V"]):
 od:
 for k from 2 to T["N"] do
  for j from 1 to k-1 do
   for x in VV[k] do
    y := `rho/PQQ`(T)(j,-1)(x);
    z := `rho/PQQ`(T)(j,+1)(x);
    C := select(w -> `is_leq/PQQ/V`(T)(x,w),VV[j]);
    if (y = z) or (C <> {y,z}) then
     return false;
    fi;
   od;
  od;
 od;
 for k from 3 to T["N"] do
  for j from 2 to k-1 do
   for i from 1 to j-1 do 
    for x in VV[k] do
     y1 := `rho/PQQ`(T)(i,-1)(x);
     y2 := `rho/PQQ`(T)(i,+1)(x);
     y3 := `rho/PQQ`(T)(i,-1)(`rho/PQQ`(T)(j,-1)(x));
     y4 := `rho/PQQ`(T)(i,-1)(`rho/PQQ`(T)(j,+1)(x));
     y5 := `rho/PQQ`(T)(i,+1)(`rho/PQQ`(T)(j,-1)(x));
     y6 := `rho/PQQ`(T)(i,+1)(`rho/PQQ`(T)(j,+1)(x));
     if not(y3 = y1 and y4 = y1 and y5 = y2 and y6 = y2) then
      reason := [i,j,k,x,y1,y2,y3,y4,y5,y6];
      return false;
     fi;
    od;
   od;
  od;
 od;
 
 return true;
end:

######################################################################

`check_UL/PQQ` := proc(T)
 global reason;
 local N,A,B,a,b,Q,kk,k,L,U,S,i,e;
 N := T["N"];
 a := T["a"];
 A := T["A"];
 B := T["B"];
 Q := T["Q1"];
 kk := T["P0_split_stage"];
 for b in B do
  k := kk[b];
  L := {seq(seq(`f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([i,e]),e in {-1,1}),i=1..k-1)};
  U := {seq(seq(`f_alt/fibre_sphere/ICP`(N)(A)(a,b,Q)([i,e]),e in {-1,1}),i=k+1..N)};
  S := {op(T["upper_fibre_part"][b])};
  if not((U intersect S = {}) and (L minus S = {})) then
   return false;
  fi;
 od:
 return true;
end:

######################################################################

`check_is_sphere/PQQ` := proc(T)
 global reason;
 local N,A,B,a,b,P0,Q0,Q1,kk,k,ee,e,C,D,E,F,u;
 N := T["N"];
 a := T["a"];
 A := T["A"];
 B := T["B"];
 P0 := T["P0"];
 Q0 := T["Q0"];
 Q1 := T["Q1"];
 kk := eval(T["P0_split_stage"]);
 ee := eval(T["P0_split_direction"]);
 for b in B do
  k := kk[b];
  e := ee[b];
  if e = -1 then 
   C := select(x -> member([x,b],Q0[k]) and member([b,x],Q0[k]),B);
   D := select(x -> member([x,b],Q1[k]) and
                    not(member([b,x],Q1[k])),C);
   E := select(x -> member([a,x],P0[k]) and
                    member([x,b],P0[k]) and
                    not(member([x,a],P0[k])) and
                    not(member([b,x],P0[k])),B);
   F := select(x -> member([x,b],Q1[k]) or member([b,x],Q1[k]),E);
  else
   C := select(x -> member([x,b],Q0[k]) and member([b,x],Q0[k]),B);
   D := select(x -> member([b,x],Q1[k]) and
                    not(member([x,b],Q1[k])),C);
   E := select(x -> member([x,a],P0[k]) and
                    member([b,x],P0[k]) and
                    not(member([a,x],P0[k])) and
                    not(member([x,b],P0[k])),B);
   F := select(x -> member([x,b],Q1[k]) or member([b,x],Q1[k]),E);
  fi;
  u := not(evalb(D = {} and F = {}));
  if u <> T["part_is_sphere"][b] then
   reason := [b,k,e,C,D,E,F]:
   return false;
  fi;
 od:
 return true;
end:

######################################################################

`check_sphere_in_ball/PQQ` := proc(T)
 global reason;
 local N,A,B,a,b,P0,Q0,Q1,US,kk,k,ee,e,C,C1,b1;
 N := T["N"];
 a := T["a"];
 A := T["A"];
 B := T["B"];
 P0 := T["P0"];
 Q0 := T["Q0"];
 Q1 := T["Q1"];
 kk := eval(T["P0_split_stage"]);
 ee := eval(T["P0_split_direction"]);
 US := eval(T["upper_fibre_part"]);
 for b in B do
  if T["part_is_sphere"][b] then
   k := kk[b];
   e := ee[b];
   if e = -1 then 
    C := select(x -> member([x,b],Q1[k]) and not(member([x,a],P0[k])),B);
    if C = {} then
     reason := [b,k,e,C];
     return false;
    fi;
    # Choose b1 to be Q1[k]-minimal in C
    C1 := C;
    while C1 <> {} do
     b1 := C1[1];
     C1 := select(x -> not(member([b1,x],Q1[k])),C1);
    od:
    if T["part_is_sphere"][b1] or
       ({op(US[b])} minus {op(US[b1])} <> {}) or
       member([b,b1],Q1[k]) then
     reason := [b,k,e,C,b1];
     return false;
    fi;
   else
    C := select(x -> member([b,x],Q1[k]) and not(member([a,x],P0[k])),B);
    if C = {} then
     reason := [b,k,e,C];
     return false;
    fi;
    # Choose b1 to be Q1[k]-maximal in C
    C1 := C;
    while C1 <> {} do
     b1 := C1[1];
     C1 := select(x -> not(member([x,b1],Q1[k])),C1);
    od:
    if T["part_is_sphere"][b1] or
       ({op(US[b])} minus {op(US[b1])} <> {}) or
       member([b1,b],Q1[k]) then
     reason := [b,k,e,C,b1];
     return false;
    fi;
   fi;
  fi;
 od:
 return true;
end:


######################################################################

`check_nonempty_interval/PQQ` := proc(T)
 local L,J,i,j,j0,j1;
 L := T["part_is_nonempty_list"];
 if not(`or`(op(L))) then return false; fi;
 J := select(i -> L[i],[seq(i,i=1..nops(L))]);
 j0 := min(op(J));
 j1 := max(op(J));
 return `and`(seq(L[j],j=j0..j1));
end:

######################################################################

`check_adjacent_nonempty/PQQ` := proc(T)
 local L,P,i;
 L := T["part_is_nonempty_list"];
 P := T["part_list"];
 for i from 1 to nops(L)-1 do
  if L[i] and L[i+1] and ({op(P[i])} intersect {op(P[i+1])} = {}) then
   return false;
  fi;
 od;
 return true;
end:

######################################################################

`check_incomparable_min/PQQ` := proc(T)
 local n,LN,RN,P,i,b,P1;
 n := nops(T["B"]);
 LN := T["left_nested_list"];
 RN := T["right_nested_list"];
 P := T["part_list"];
 for i from 1 to n-1 do
  if not(LN[i+1]) and not(RN[i]) then
   b := T["Q1_tot"][i];
   P1 := `m/fibre_sphere/ICP`(T["N"])(T["A"])(a,b,T["Q1"]):
   if not (member(P1,{op(P[i])}) and member(P1,{op(P[i+1])})) then
    return false;
   fi;
  fi;
 od;
 return true;
end:

######################################################################

`check_intersections_nested/PQQ` := proc(T)
 global reason;
 local n,P,PS,i,j,k;
 n := nops(T["B"]);
 P := T["part_list"];
 for i from 1 to n do PS[i] := {op(P[i])}; od:
 for i from 1 to n-2 do
  for j from i+1 to n-1 do
   for k from j+1 to n do
    if (PS[i] intersect PS[k]) minus PS[j] <> {} then
     reason := [i,j,k];
     return false;
    fi;
   od;
  od;
 od;
 return true;
end:

