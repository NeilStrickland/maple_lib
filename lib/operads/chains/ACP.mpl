######################################################################

`is_element/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local procname_,i,U,V;

 global reason;

 procname_ := "is_element/ACP";
 
 if not (type(Q,list) and nops(Q) = N) then
  reason := [procname_,"Q is not a list of length N",Q,N];
  return false;
 fi;

 for i from 1 to N do
  if not `is_element/preord`(A)(Q[i]) then
   reason := [procname_,"Q[i] is not a preorder on A",Q[i],A,reason];
   return false;
  fi;
 od;

 if not `is_total/preord`(A)(Q[1]) then
  reason := [procname_,"Q[1] is not total",Q[1]];
  return false;  
 fi;

 for i from 1 to N-1 do
  U := Q[i] intersect `op/preord`(A)(Q[i]);
  V := Q[i+1] union `op/preord`(A)(Q[i+1]);
  if U <> V then
   reason := [procname_,"Q[i] and Q[i+1] do not match",Q[i],Q[i+1]];
   return false;
  fi;
 od;

 return true;
end:

`is_equal/ACP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 local procname_;
 global reason;

 procname_ := "is_equal/ACP";
 
 if Q1 <> Q2 then
  reason := [procname_,"Q1 <> Q2",Q1,Q2];
  return false;
 fi;

 return true;
end:

`is_leq/ACP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 local i;

 for i from 1 to N do 
  if Q2[i] minus Q1[i] <> {} then
   return false;
  fi;
 od;

 return true;
end:

`list_elements/ACP` := (N::posint) -> proc(A::set)
 local W,X,Y,Z,Q,R,S,pi,B;

 if nops(A) = 0 then
  return FAIL;
 fi;

 if N = 1 then
  X := `list_elements/total_preord`(A);
  return map(Q -> [Q],X);
 fi;

 X := `list_elements/ACP`(N-1)(A);
 Y := NULL;
 
 for Q in X do
  pi := `block_partition/preord`(A)(Q[N-1]);
  Z := [{}];
  for B in pi do
   W := `list_elements/total_preord`(B);
   Z := [seq(seq(R union S,S in W),R in Z)];
  od:
  Y := Y,seq([op(Q),R],R in Z);
 od;
 return [Y];
end:

`count_elements/ACP` := (N::posint) -> proc(A::set)
 local d;
 add(Stirling2(nops(A),d)*d!*N^(d-1),d=1..nops(A)); 
end:

`random_element/ACP` := (N::posint) -> (A::set) -> proc()
 local i,n,pi,Q,R,S,B,C;

 if nops(A) = 0 then
  return FAIL;
 fi;

 R := `random_element/total_preord`(A)();
 Q := [R];
 for i from 2 to N do 
  pi := `block_partition/preord`(A)(R);
  R := {};
  for B in pi do
   S := `random_element/total_preord`(B)();
   R := R union S;
  od;
  Q := [op(Q),R];
 od;

 return Q;
end:

`rank_vector/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local i;
 [seq(`rank/preord`(N)(A)(Q[i]),i=1..N)];
end:

`rank/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local i;
 add(`rank/preord`(N)(A)(Q[i]),i=1..N);
end:

`res/ACP` := (N::posint) -> (A::set,B::set) -> proc(Q)
 return map(`intersect`,Q,`top/autorel`(B));
end:

`is_constant/ACP` := (N::posint) -> (A::set) -> proc(Q)
 return evalb(nops(Q[N]) = nops(A)^2);
end;

`is_separated/ACP` := (N::posint) -> (A::set) -> proc(Q)
 return evalb(Q[N] minus `id/autorel`(A) = {});
end;

`bot/ACP` := (N::posint) -> (A::set) -> [`top/autorel`(A) $ N];

######################################################################

`mu/W/ACP` := (N::posint) -> (A::set) -> proc(x) 
 local QT,ET,AA,i,a,b;

 QT := table():
 ET := table():
 AA := {seq(seq([a,b],b in A),a in A)};
 ET[0] := AA;

 for i from 1 to N do
  QT[i] := select(ab -> is(x[ab[1]][i] <= x[ab[2]][i]),ET[i-1]);
  ET[i] := QT[i] intersect `op/autorel`(A)(QT[i]);
 od:
 
 return [seq(QT[i],i=1..N)];
end:

`sigma/ACP/W` := (N::posint) -> (A::set) -> proc(Q)
 local u,x,a,i;

 u := [seq(`rank_table/preord`(A)(Q[i]),i=1..N)];
 x := table():
 for a in A do 
  x[a] := [seq(u[i][a],i=1..N)];
 od:

 return eval(x);
end;

######################################################################

`is_element/realisation/ACP` := (N::posint) -> (A::set) -> 
 `is_element/realisation/generic`("ACP",
  eval(`is_element/ACP`(N)(A)),
  eval(`is_leq/ACP`(N)(A))
 );

`is_equal/realisation/ACP` := (N::posint) -> (A::set) -> 
 `is_equal/realisation/generic`("ACP",
  eval(`is_equal/ACP`(N)(A))
 );

`sigma/realisation/ACP/W` := (N::posint) -> (A::set) -> proc(u)
 local x,y,m,a,Q,S;

 x := table();
 for a in A do
  x[a] := [0$N];
 od:

 S := map(op,[indices(u)]);
 for Q in S do 
  y := `sigma/ACP/W`(N)(A)(Q);
  m := u[Q];
  for a in A do 
   x[a] := x[a] +~ (m *~ y[a]);
  od:
 od:

 return eval(x);
end;

`mu_aux/ACP` := (N::posint) -> (A::set) -> proc(x)
 local Q,t,i,ab,a,b,s,y,u;

 Q := `mu/W/ACP`(N)(A)(x);

 if nops(Q[N]) = nops(A)^2 then
  return(table());
 fi;

 t := 1;
 for i from 1 to N do
  for ab in Q[i] minus `op/autorel`(A)(Q[i]) do
   a,b := op(ab);
   t := min(t,x[b][i] - x[a][i]);
  od;
 od;

 s := `sigma/ACP/W`(N)(A)(Q);
 y := table();
 for a in A do 
  y[a] := x[a] -~ (t *~ s[a]);
 od;

 u := `mu_aux/ACP`(N)(A)(y);
 if `is_element/RR`(u[Q]) then 
  u[Q] := u[Q] + t;
 else
  u[Q] := t;
 fi;

 return eval(u);
end;

######################################################################

`rank_vector/ACP` := (N) -> (A) -> proc(Q)
 local i;
 return [seq(`rank/preord`(A)(Q[i])-1,i=1..N)];
end;

`rank/ACP` := (N) -> (A) -> proc(Q)
 return `+`(op(`rank_vector/ACP`(N)(A)(Q)));
end;


`cofunctor/ACP` := (N::posint) -> (A::set,B::set) -> (f) -> proc(Q)
 map(`cofunctor/autorel`(A,B)(f),Q);
end;

######################################################################

`is_element/split_spots/ACP` := (N::posint) -> (A::set) -> (Q) -> proc(iCD)
 global reason;
 local procname_,i,B,C,D,B1,E,C1;

 procname_ := "is_element/split_spots/ACP";
 
 if not(type(iCD,list) and nops(iCD) = 3) then
  reason := [procname_,"iCD is not a list of length 3",iCD];
  return false;
 fi;

 i,C,D := op(iCD);
 if not(type(i,posint) and i <= N) then
  reason := [procname_,"i is not in [1,N]",i,N];
  return false;
 fi;

 if not(type(C,set) and nops(C) > 0 and C minus A = {}) then
  reason := [procname_,"C is not a nonempty subset of A",C,A];
  return false;
 fi;

 if not(type(D,set) and nops(D) > 0 and D minus A = {}) then
  reason := [procname_,"D is not a nonempty subset of A",D,A];
  return false;
 fi;

 if C intersect D <> {} then
  reason := [procname_,"C and D are not disjoint",C,D];
  return false;
 fi;

 B := C union D;
 
 B1 := select(a -> member([a,B[1]],Q[i]) and member([B[1],a],Q[i]),A);
 if B1 <> B then
  reason := [procname_,"C u D is not an equivalence class for Q[i]",C,D,i,Q[i]];
  return false;
 fi;

 if i < N then
  E := select(ab -> member([ab[2],ab[1]],Q[i+1]),Q[i+1]);
  C1 := map(ab -> ab[1],select(ab -> member(ab[1],C),E));
  if C minus C1 <> {} then
   reason := [procname_,"C is not a union of equivalence classes for Q[i+1]",C,D,i,Q[i+1]];
   return false;
  fi;
 fi;

 return true;
end:

######################################################################

`list_elements/split_spots/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local E,L,i,B,m,UU,U,CC,C,a;

 E := [seq(`block_partition/preord`(A)(Q[i]),i=1..N),{seq({a},a in A)}];
 L := NULL;
 for i from 1 to N do
  for B in E[i] do
   UU := select(U -> U minus B = {},E[i+1]);
   m := nops(UU);
   UU := select(U -> nops(U) < m,`list_elements/nonempty_subsets`(UU));
   CC := map(U -> map(op,U),UU);
   L := L,seq([i,C,B minus C],C in CC);
  od: 
 od:
 return [L];
end:

######################################################################

`split/ACP` := (N::posint) -> (A::set) -> (Q) -> proc(iCD)
 local i,j,C,D,CD,DC,c,d;

 i,C,D := op(iCD);
 CD := {seq(seq([c,d],d in D),c in C)};
 DC := {seq(seq([d,c],d in D),c in C)};
 return([
  seq(Q[j],j=1..i-1),
  Q[i] minus DC,
  seq(Q[j] minus DC minus CD,j=i+1..N)
 ]);
end:

######################################################################

`is_element/glue_spots/ACP` := (N::posint) -> (A::set) -> (Q) -> proc(iCDS)
 global reason;
 local procname_,i,C,D,S,Qi,Qis,Ei,C1,D1,E,nC,nD;

 procname_ := "is_element/glue_spots/ACP";
 
 if not(type(iCDS,list) and nops(iCDS) = 4) then
  reason := [procname_,"iCDS is not a list of length 4",iCDS];
  return false;
 fi;

 i,C,D,S := op(iCDS);
 if not(type(i,posint) and i <= N) then
  reason := [procname_,"i is not in [1,N]",i,N];
  return false;
 fi;

 if not(type(C,set) and nops(C) > 0 and C minus A = {}) then
  reason := [procname_,"C is not a nonempty subset of A",C,A];
  return false;
 fi;

 if not(type(D,set) and nops(D) > 0 and D minus A = {}) then
  reason := [procname_,"D is not a nonempty subset of A",D,A];
  return false;
 fi;

 if C intersect D <> {} then
  reason := [procname_,"C and D are not disjoint",C,D];
  return false;
 fi;

 Qi := Q[i];
 Ei,Qis := selectremove(ab -> member([ab[2],ab[1]],Qi),Qi);

 if not(member([C[1],D[1]],Qis)) then
  reason := [procname_,"not(C < D)",C,D,Qi];
  return false;
 fi;

 C1 := select(a -> member([a,C[1]],Ei),A);
 if C1 <> C then
  reason := [procname_,"C is not an equivalence class",C,C1,Qi];
  return false;
 fi;

 D1 := select(a -> member([a,D[1]],Ei),A);
 if D1 <> D then
  reason := [procname_,"D is not an equivalence class",D,D1,Qi];
  return false;
 fi;

 E := select(a -> member([C[1],a],Qis) and member([a,D[1]],Qis),A);
 if E <> {} then
  reason := [procname_,"C and D are not adjacent",C,D,E,Qi];
  return false;
 fi;

 if i = N then
  if S = {} then
   return true;
  else
   reason := [procname_,"i=N but S <> {}",i,N,S];
   return false;
  fi;
 fi;

 nC := nops(`block_partition/preord`(C)(`res/preord`(A,C)(Q[i+1])));
 nD := nops(`block_partition/preord`(D)(`res/preord`(A,D)(Q[i+1])));

 if not (type(S,set(posint)) and
         nops(S) = nC and
         max(op(S)) <= nC+nD) then
  reason := [procname_,"S is not a subset of size nC in [1,nC+nD]",S,C,D,Q[i+1]];
  return false;
 fi;

 return true;
end:

######################################################################

`list_elements/glue_spots/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local L,i,j,Qi,Qis,E,E0,E1,B,U,C,a,b,r0,nn,SS,S;

 L := NULL;
 for i from 1 to N do
  Qi := Q[i];
  Qis := remove(ab -> member([ab[2],ab[1]],Qi),Qi);
  E := `block_partition/preord`(A)(Qi);
  E0 := NULL;
  E1 := table():
  for B in E do 
   E0 := E0,B[1];
   E1[B[1]] := B;
  od:
  E0 := {E0}:
  U := table():
  C := table():
  for a in E0 do 
   U[a] := select(b -> member([a,b],Qis),E0);
  od: 
  for a in E0 do 
   C[a] := U[a] minus {seq(op(U[b]),b in U[a])};
  od:
  if i < N then
   r0 := `rank_table/preord`(A)(Q[i+1]);
   for a in E0 do 
    nn[a] := 1 + max(seq(r0[b],b in E1[a]));
   od;
  fi;

  for a in E0 do 
   for b in C[a] do
    if i < N then
     SS := combinat[choose]({seq(j,j=1..nn[a]+nn[b])},nn[a]);
    else
     SS := {{}};
    fi;
    L := L,seq([i,E1[a],E1[b],S],S in SS);
   od;
  od;
 od:
 return [L];
end:

######################################################################

`glue/ACP` := (N::posint) -> (A::set) -> (Q) -> proc(iCDS)
 local i,C,D,S,CD,DC,c,d,P,j,k,rc,rd,nc,nd,ic,id,n,Cn,Dn,BB,x,y;

 i,C,D,S := op(iCDS);
 CD := {seq(seq([c,d],d in D),c in C)};
 DC := {seq(seq([d,c],d in D),c in C)};
 P := table():
 for j from 1 to i-1 do 
  P[j] := Q[j];
 od:
 P[i] := Q[i] union DC;
 if i < N then
  rc := `rank_table/preord`(C)(Q[i+1]);
  rd := `rank_table/preord`(D)(Q[i+1]);
  nc := max(seq(rc[c],c in C)) + 1;
  nd := max(seq(rd[d],d in D)) + 1;
  for n from 1 to nc do Cn[n] := select(c -> rc[c] = n-1,C); od;
  for n from 1 to nd do Dn[n] := select(d -> rd[d] = n-1,D); od;
  ic := 0;
  id := 0;
  BB := NULL;
  for j from 1 to nc + nd do
   if member(j,S) then
    ic := ic+1;
    BB := BB,Cn[ic];
   else
    id := id+1;
    BB := BB,Dn[id];
   fi;
  od;
  BB := [BB];
  P[i+1] := Q[i+1] union {seq(seq(seq(seq([x,y],y in BB[k]),x in BB[j]),k=j..nc+nd),j=1..nc+nd)};
 fi;
 for j from i+2 to N do
  P[j] := Q[j];  
 od:
 return [seq(P[j],j=1..N)];
end:

######################################################################

`describe/ACP` := (N::posint) -> (A::set) -> proc(Q)
 local s,E,i,j,k,r,s0,s1,s2,B,C,m;

 s := "";
 E := {A};
 for i from 1 to N do
  s0 := "";
  for B in E do
   if nops(B) > 1 then
    r := `rank_table/preord`(B)(Q[i] intersect `top/autorel`(B));
    m := max(map(b -> r[b],B));
    s1 := "";
    for j from 0 to m do 
     C := select(b -> r[b]=j,B);
     s2 := "";
     for k from 1 to nops(C) do 
      s2 := cat(s2,`if`(k>1,"=",""),sprintf("%A",C[k]));
     od:
     s1 := cat(s1,`if`(j>0,"<",""),s2);
    od;
    s0 := cat(s0,`if`(s0="","",","),s1);
   fi;
  od:
  s := cat(s,`if`(s="","",";"),s0);
  E := `block_partition/preord`(A)(Q[i]);
 od;
 s := cat("(",s,")");
end:
