######################################################################

`is_element/SCP` := (N::posint) -> (A::set) -> proc(Q)
 local i,U,V;

 global reason;

 if not `is_element/ACP`(N)(A)(Q) then
  reason := [convert(procname,string),"Q in ACP(N)(A)",reason];
  return false;
 fi;

 if nops(Q[N]) = nops(A)^2 then
  reason := [convert(procname,string),"Q[N] has only one block",Q[N]];
  return false;
 fi;

 return true;
end:

`is_equal/SCP` := (N::posint) -> (A::set) -> proc(Q1,Q2)
 global reason;

 if Q1 <> Q2 then
  reason := [convert(procname,string),"Q1 <> Q2",Q1,Q2];
  return false;
 fi;

 return true;
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

`list_elements/SCP` := (N::posint) -> proc(A::set)
 local X,n;
 n := nops(A);
 X := `list_elements/ACP`(N)(A);
 X := select(Q -> nops(Q[N]) < n^2,X);
 return X;
end:

`count_elements/SCP` := (N::posint) -> (A::set) -> add(Stirling2(nops(A),d)*d!*N^(d-1),d=2..nops(A)); 

`random_element/SCP` := (N::posint) -> (A::set) -> proc()
 local i,n,pi,Q,R,S,B,C,ok;

 if nops(A) <= 1 then
  return FAIL;
 fi;

 ok := false;

 while not ok do 
  Q := `random_element/ACP`(N)(A)();
  if nops(Q[N]) < nops(A)^2 then
   ok := true;
  fi;
 od;

 return Q;
end:


`res/SCP` := (N::posint) -> (A::set,B::set) -> proc(Q)
 return map(`intersect`,Q,`top/autorel`(B));
end:

######################################################################

`gamma/SCP` := (N::posint) -> (A::set) -> proc(Q)
 [seq(`op/autorel`(A)(Q[i]) minus Q[i],i=1..N)];
end:

######################################################################

`mu/SW/SCP` := (N::posint) -> (A::set) -> proc(x) 
 return `mu/W/ACP`(N)(A)(x);
end:

`sigma/SCP/SW` := (N::posint) -> (A::set) -> proc(Q)
 return `bottom_normalise/SW`(N)(A)(`sigma/ACP/W`(N)(A)(Q));
end;

######################################################################

`describe/SCP` := eval(`describe/ACP`):

