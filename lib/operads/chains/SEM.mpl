######################################################################

`is_element/SEM` := (N::posint) -> (A::set) -> proc(eta)
 local AA,a,b,c,ok;
 global reason;

 if not(type(eta,table)) then
  reason := [convert(procname,string),"eta is not a table",eta];
  return false;
 fi;

 AA := [seq(seq([a,b],b in A),a in A)];
 if {indices(eta)} <> {op(AA)} then
  reason := [convert(procname,string),"eta is not indexed by A^2",eta,AA];
  return false;
 fi; 

 for a in A do
  for b in A do
   if eta[a,b] = 0 and a <> b then
    reason := [convert(procname,string),"eta does not separate a and b",a,b,eta];
    return false;
   fi;

   if eta[a,b] + eta[b,a] <> 0 then
    reason := [convert(procname,string),"eta is not antisymmetric at [a,b]",a,b,eta];
    return false;
   fi;

   for c in A do
    ok := `is_leq/E`(N)(0,eta[a,c]) or 
          `is_leq/E`(N)(eta[a,b],eta[a,c]) or 
          `is_leq/E`(N)(eta[b,c],eta[a,c]);
    if not(ok) then
     reason := [convert(procname,string),"min(0,eta[a,b],eta[a,c]) > eta[a,c]",a,b,c,eta];
     return false;
    fi;

    ok := `is_leq/E`(N)(eta[a,c],0) or 
          `is_leq/E`(N)(eta[a,c],eta[a,b]) or 
          `is_leq/E`(N)(eta[a,c],eta[b,c]);
    if not(ok) then
     reason := [convert(procname,string),"eta[a,c] > max(0,eta[a,b],eta[a,c])",a,b,c,eta];
     return false;
    fi;
   od;
  od;
 od;

 return true;
end;

`is_equal/SEM` := (N::posint) -> (A::set) -> proc(eta,zeta)
 local a,b;
 global reason;

 for a in A do
  for b in A do
   if eta[a,b] <> zeta[a,b] then
    reason := [convert(procname,string),"eta[a,b] <> zeta[a,b]",a,b,eta[a,b],zeta[a,b]];
    return false;
   fi;
  od;
 od;

 return true;
end:

`is_leq/SEM` := (N::posint) -> (A::set) -> proc(eta,zeta)
 local a,b;

 for a in A do
  for b in A do
   if not(`preceq/E`(N)(A)(eta[a,b],zeta[a,b])) then
    return false;
   fi;
  od;
 od;

 return true;
end:

`build/SEM` := (N::posint) -> (A::set) -> proc(s::list,u::list) 
 local n,L,i,j,k,m,eta,a,b;

 n := nops(A);
 if nops(s) <> n or nops(u) <> n-1 then return FAIL; fi;
 if {op(s)} <> A then return FAIL; fi;

 L := table();
 for i from 1 to n do
  L[s[i]] := i;
 od:

 eta := table;

 for a in A do
  eta[a,a] := 0;
  for b in A do
   i := L[a];
   j := L[b];
   if i < j then
    m := min(seq(u[k],k=i..j-1));
    eta[a,b] :=  epsilon^m;
    eta[b,a] := -epsilon^m;
   fi;
  od;
 od;

 return eval(eta);
end:

`random_element/SEM` := (N::posint) -> (A::set) -> proc()
 local s,m,u,i;
 
 s := `random_element/ord`(A)();
 m := nops(A);
 u := [seq(rand(0..N-1)(),i=1..m-1)];
 return `build/SEM`(N)(A)(s,u);
end:

`list_elements/SEM` := (N::posint) -> proc(A::set)
 option remember;
 local S,U,s,u,m,i,j;

 S := `list_elements/ord`(A);
 U := [[]];
 m := nops(A);
 for i from 1 to m-1 do
  U := map(u -> seq([op(u),j],j=0..N-1),U);
 od: 

 return [seq(seq(`build/SEM`(N)(A)(s,u),u in U),s in S)];
end:

`count_elements/SEM` := (N::posint) -> (A::set) ->
  nops(A)! * N^(nops(A) - 1);
  
`mu/F/SEM` := (N::posint) -> (A::set) -> proc(x)
 local eta,a,b,u,v,i;

 eta := table();
 for a in A do
  for b in A do
   u := x[b] -~ x[a];
   v := add(u[i] * epsilon^(i-1),i = 1..N);
   eta[a,b] := `lambda/P/E`(N)(v);
  od;
 od;

 return eval(eta);
end:

`sigma/SEM/F` := (N::posint) -> (A::set) -> proc(eta)
 local n,m,a,b,A1,x,u,i;

 n := table():

 for a in A do
  for b in A do
   n[a,b] := `is_leq/E`(N)(0,eta[a,b]);
  od;
 od;

 A1 := sort([op(A)],(a,b) -> n[a,b]);

 x := table():
 u := 0;
 m := nops(A1);
 x[A1[1]] := [0$N];

 for i from 2 to m do
  u := u + eta[A1[i-1],A1[i]];
  x[A1[i]] := [seq(coeff(u,epsilon,i),i=0..N-1)];
 od;

 return(eval(x));
end:
