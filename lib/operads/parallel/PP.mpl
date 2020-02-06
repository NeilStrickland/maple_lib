######################################################################

`is_element/PP` := (N::posint) -> (A::set) -> proc(R)
 local E,i;
 global reason;
 
 if not(type(R,list) and nops(R) = N) then
  reason := [convert(procname,string),"R is not a list of length N",R,N];
  return false;
 fi;

 E := {seq(seq([a,b],b in A),a in A)};
 
 for i from 1 to N do
  if not `is_element/preord`(A)(R[i]) then
   reason := [convert(procname,string),"R[i] is not a preorder on A",R,i,A,reason];
   return false;
  fi;

  E := E intersect R[i] intersect `op/preord`(A)(R[i]);
 od;

 if E <> {seq([a,a],a in A)} then
  reason := [convert(procname,string),"E <> Delta",E];
  return false;
 fi;

 return true;
end:

`is_equal/PP` := (N::posint) -> (A::set) -> proc(R,S)
 local i;
 global reason;

 for i from 1 to N do
  if not(`is_equal/preord`(A)(R[i],S[i])) then
   reason := [convert(procname,string),"R[i] <> S[i]",i,R[i],S[i]];
   return false;
  fi;
 od;

 return true;
end:

`is_leq/PP` := (N::posint) -> (A::set) -> proc(R,S)
 local i;
 global reason;

 for i from 1 to N do
  if not(`is_leq/preord`(A)(R[i],S[i])) then
   reason := [convert(procname,string),"R[i] is not a subset of S[i]",i,R[i],S[i]];
   return false;
  fi;
 od;

 return true;
end:

`mu/F/PP` := (N::posint) -> (A::set) -> proc(x)
 local AA;
 
 AA := {seq(seq([a,b],b in A),a in A)};
 
 [seq(select(ab -> x[ab[1]][i] <= x[ab[2]][i],AA),i=1..N)];
end:

`sigma/PP/F` := (N::posint) -> (A::set) -> proc(R)
 local x0,x,r,a,i;

 x0 := table();
 for i from 1 to N do
  r := eval(`rank_table/preord`(A)(R[i]));
  for a in A do x0[a,i] := r[a]; od;
 od;

 x := table();
 for a in A do x[a] := [seq(x0[a,i],i=1..N)]; od;

 return eval(x);
end;

`random_element/PP` := (N::posint) -> (A::set) -> proc()
 local R,ok;

 ok := false;
 while not(ok) do
  R := [seq(`random_element/preord`(A),i=1..N)];
  ok := `is_element/PP`(N)(A)(R);
 od;

 return R;
end;

`list_elements/PP` := (N::posint) -> proc(A::set)
 local RR,QQ,R,i;

 RR := `list_elements/preord`(A);
 QQ := [[]];
 for i from 1 to N do
  QQ := [seq(seq([op(Q),R],R in RR),Q in QQ)];
 od;

 QQ := select(`is_element/PP`(N)(A),QQ);

 return QQ;
end;

######################################################################

`is_element/realisation/PP` := (N::posint) -> (A::set) -> 
 `is_element/realisation/generic`("PP",
  eval(`is_element/PP`(N)(A)),
  eval(`is_leq/PP`(N)(A))
 );

`is_equal/realisation/PP` := (N::posint) -> (A::set) -> 
 `is_equal/realisation/generic`("PP",
  eval(`is_equal/PP`(N)(A))
 );

