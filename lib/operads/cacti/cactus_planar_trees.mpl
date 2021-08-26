######################################################################

`is_element/cactus_planar_trees` := (A::set) -> proc(Js)
 global reason;
 local tag,J,s,sss,B,C,E,i0,i1,i2,e0,e1,e2,m,j,a;

 tag := "is_element/cactus_planar_trees";

 if A = {} then
  reason := [tag,"A is empty"];
  return false;
 fi;

 if not(type(Js,list) and nops(Js) = 2) then
  reason := [tag,"Js is not a list of length 2",Js];
  return false;
 fi;

 J,s := op(Js);

 if not(`is_element/cactus_trees`(A)(J)) then
  reason := [tag,"J is not a pre cactus tree",J,reason];
 fi;
 
 E := {seq(seq([a,j],a in j),j in J)};

 if not `is_element/cycord`(E)(s) then
  reason := [tag,"s is not a cyclic ordering of E",s,E];
  return false;
 fi;

 m := nops(s);
 sss := map(op,[s,s,s]);
 for i0 from 1 to m do
  e0 := s[i0];
  i1 := i0+1;
  while sss[i1][1] <> e0[1] do i1 := i1+1; od;
  e1 := sss[i1];
  i2 := i1+1;
  while sss[i2][2] <> e1[2] do i2 := i2+1; od;
  if sss[i2] <> e0 then
   reason := [tag,"bad permutation structure",s,i0,i1,i2];
  fi;
 od:
 return true;
end:

`is_equal/cactus_planar_trees` := (A::set) -> proc(Js0,Js1)
 local J0,J1,s0,s1,s2,n,i;

 J0,s0 := op(Js0);
 J1,s1 := op(Js1);

 if J0 <> J1 then return false; fi;
 if nops(s0) <> nops(s1) then return false; fi;

 n := nops(s0);
 if n = 0 then return true; fi;
 
 i := 1;
 while i <= n and s1[i] <> s0[1] do i := i+1; od;

 if i > n then return false; fi;
 s2 := [op(i..-1,s1),op(1..(i-1),s1)];

 return evalb (s0 = s2);
end:

######################################################################

# There is a good partial order on this set, but we have not yet
# written code for it.

`is_leq/cactus_planar_trees` := NULL:

######################################################################

`glue_cycles/cactus_planar_trees` := (A::set) -> (J) -> proc(sA,sJ)
 local fA,fJ,a,j,m,n,i,u,v,s;

 fA := table():
 fJ := table():
 for a in A do
  m := nops(sA[a]);
  for i from 1 to m do
   fA[[a,sA[a][i]]] := [a,sA[a][`if`(i<m,i+1,1)]];
  od;
 od:
 for j in J do
  m := nops(sJ[j]);
  for i from 1 to m do
   fJ[[sJ[j][i],j]] := [sJ[j][`if`(i<m,i+1,1)],j];
  od:
 od:

 u := [J[1][1],J[1]];
 v := fJ[fA[u]];
 s := u;
 n := `+`(op(map(nops,[op(J)])));
 for i from 1 to n-1 do
  s := s,v;
  v := fJ[fA[v]];
 od:

 return [s];
end:

`split_cycles/cactus_planar_trees` := (A::set) -> (J) -> proc(s)
 local sA,sJ,a,j;
 
 sA := table():
 sJ := table():
 for a in A do
  sA[a] := map(e -> e[2],select(e -> e[1] = a,s));
 od:
 for j in J do
  sJ[j] := map(e -> e[1],select(e -> e[2] = j,s));
 od:

 return [eval(sA),eval(sJ)];
end:

######################################################################

`list_elements/cactus_planar_trees` := proc(A::set)
 local L,M,J,JJ,a,j,SA,SJ,sA,sJ,V,W,u,v,w;

 if nops(A) = 0 then
  return [];
 elif nops(A) = 1 then
  return [[{},[]]];
 fi;
 
 L := `list_elements/cactus_trees`(A);
 M := NULL;
 for J in L do
  JJ := table():
  for a in A do JJ[a] := select(j -> member(a,j),J); od:
  SA := [[]]:
  for a in A do
   V := `list_elements/cycord`(JJ[a]);
   SA := [seq(seq([op(u),a = v],u in SA),v in V)];
  od:
  SA := map(table,SA);
  SJ := [[]]:
  for j in J do
   W := `list_elements/cycord`(j);
   SJ := [seq(seq([op(u),j = w],u in SJ),w in W)];
  od:
  SJ := map(table,SJ);
  M := M,seq(seq([J,`glue_cycles/cactus_planar_trees`(A)(J)(sA,sJ)],sJ in SJ),sA in SA);
 od:
 return [M];
end:

######################################################################

`count_elements/cactus_planar_trees` := NULL:

######################################################################

`random_element/cactus_planar_trees` := (A::set) -> proc()
 local J,sA,sJ,JJ,a,j,s;

 if nops(A) = 0 then
  return FAIL;
 elif nops(A) = 1 then
  return [{},[]];
 fi;
 
 J := `random_element/cactus_trees`(A)();
 sA := table();
 sJ := table();
 for a in A do
  JJ[a] := select(j -> member(a,j),J);
  sA[a] := `random_element/cycord`(JJ[a])();
 od;
 for j in J do
  sJ[j] := `random_element/cycord`(j)();
 od:
 s := `glue_cycles/cactus_planar_trees`(A)(J)(sA,sJ);
 return [J,s];
end:
