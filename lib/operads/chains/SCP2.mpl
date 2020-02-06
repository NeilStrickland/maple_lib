######################################################################

`is_element/SCP2` := (N::posint) -> (A::set,B::set) -> proc(QP)
 local i,Q0,Q,P;

 global reason;

 if not(type(QP,list) and nops(QP) = 2) then
  reason := [convert(procname,string),"QP is not a list of length two",reason];
 fi;

 Q,P := op(QP);

 if not `is_element/SCP`(N)(A)(Q) then
  reason := [convert(procname,string),"Q not in SCP(N)(A)",reason];
  return false;
 fi;

 if not `is_element/SCP`(N)(B)(P) then
  reason := [convert(procname,string),"P not in SCP(N)(B)",reason];
  return false;
 fi;

 Q0 := `res/SCP`(N)(A,B)(Q);

 if Q0 <> P and Q0 <> [`top/autorel`(B)$N] then
  reason := [convert(procname,string),"Q and P are incompatible"];
  return false;
 fi;

 return true;
end:

`is_equal/SCP2` := (N::posint) -> (A::set,B::set) -> proc(QP1,QP2)
 return 
  `is_equal/SCP`(N)(A)(QP1[1],QP2[1]) and
  `is_equal/SCP`(N)(B)(QP1[2],QP2[2]);
end:

`is_leq/SCP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 local i;

 for i from 1 to N do 
  if Q2[i] minus Q1[i] <> {} then
   return false;
  fi;
 od;

 return true;
end:

`list_elements/SCP2` := (N::posint) -> proc(A::set,B::set)
 local X,Y,Z,n,Q,P;

 X := `list_elements/SCP`(N)(A);
 Y := `list_elements/SCP`(N)(B);
 Z := NULL;

 n := nops(B);

 for Q in X do
  P := `res/SCP`(N)(A,B)(Q);

  if nops(P[N]) = n^2 then
   Z := Z,seq([Q,P],P in Y);
  else
   Z := Z,[Q,P];
  fi;
 od:

 Z := [Z];

 return Z;
end:

`random_element/SCP2` := (N::posint) -> (A::set,B::set) -> proc(p := 0.5)
 local A0,p0,a,Q0,AA,Q,P;
 if rand(1..10000)() < evalf(10000 * p) then
  A0 := (A minus B) union {b0};
  p0 := table();
  for a in A do 
   p0[a] := `if`(member(a,B),b0,a);
  od;
  Q0 := `random_element/SCP`(N)(A0)();
  AA := `top/autorel`(A);
  Q := [seq(select(xy -> member(map(p0,xy),Q0[i]),AA),i=1..N)];
  P := `random_element/SCP`(N)(B)();
  return [Q,P];
 else
  Q := `random_element/SCP`(N)(A)();
  P := `res/SCP`(N)(A,B)(Q);

  while `is_constant/ACP`(N)(B)(P) do
   Q := `random_element/SCP`(N)(A)();
   P := `res/SCP`(N)(A,B)(Q);
  od;

  return [Q,P];
 fi;
end:



