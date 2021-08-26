`is_element/ICP_alt` := (N::posint) -> (A::set) -> proc(Ru)
 local n,R,u;
 global reason;

 n := nops(A);
 if n = 0 then
  reason := [convert(procname,string),"A is empty"];
  return false;
 fi;

 if not(type(Ru,list) and nops(Ru) = 2) then
  reason := [convert(procname,string),"Ru is not a list of length two"];
  return false;
 fi;

 R,u := op(Ru);

 if not `is_element/ord`(A)(R) then
  reason := [convert(procname,string),"R is not an order on A",reason];
  return false;
 fi;

 if not(type(u,list(posint)) and
        nops(u) = n-1 and
        max(op(u)) <= N) then
  reason := [convert(procname,string),"u is not in [1,N]^(n-1)"];
  return false;  
 fi;

 return true;
end:

`is_equal/ICP_alt` := (N::posint) -> (A::set) -> proc(Ru1,Ru2)
 global reason;

 if Ru1 <> Ru2 then
  reason := [convert(procname,string),"Ru1 <> Ru2",Ru1,Ru2];
  return false;
 fi;

 return true;
end:

`list_elements/ICP_alt` := (N::posint) -> proc(A::set)
 local RR,uu,n,R,u,i;

 RR := `list_elements/ord`(A);
 n := nops(A);
 uu := [[]];
 for i from 1 to n-1 do
  uu := [seq(seq([op(u),i],i=1..N),u in uu)];
 od: 

 return [seq(seq([R,u],u in uu),R in RR)];
end:

`random_element/ICP_alt` := (N::posint) -> (A::set) -> proc()
 local R,u,i;

 R := `random_element/ord`(A)();
 u := [seq(rand(1..N)(),i=1..nops(A)-1)];
 return [R,u];
end:

`count_elements/ICP_alt` := (N::posint) -> proc(A::set)
 local n;

 n := nops(A);
 return n! * N^(n-1);
end: 



