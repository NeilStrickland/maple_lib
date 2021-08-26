######################################################################

`is_element/P2` := (N::posint) -> (A::set) -> proc(u)
 local n,A2,ab,ba,v,i;
 global reason;

 if not(type(u,table)) then
  reason := [convert(procname,string),"u is not a table",u];  
  return false;
 fi;

 n := nops(A);

 A2 := `list_elements/pairs`(A);
 if {indices(u)} <> {op(A2)} then
  reason := [convert(procname,string),"u is not indexed by pairs in A",u,A2];  
  return false;
 fi;

 for ab in A2 do
  v := u[op(ab)];
  if not(`is_element/R`(N)(v)) then
   reason := [convert(procname,string),"u[a,b] is not in R^N",op(ab),v,N];  
   return false;
  fi;
  if simplify(add(v[i]^2,i=1..N) - 1) <> 0 then
   reason := [convert(procname,string),"u[a,b] is not in S^(N-1)",op(ab),v,N];  
   return false;
  fi;
 od;

 for ab in A2 do
  ba := [ab[2],ab[1]];
  if u[op(ab)] +~ u[op(ba)] <> [0$N] then
   reason := [convert(procname,string),"u[a,b]+u[b,a] <> 0",op(ab),u[op(ab)],u[op(ba)],N];  
   return false;
  fi;
 od;

 return true;
end:

`phi2/Fbar/P2` := (N::posint) -> (A::set) -> proc(x)
 local A2,u,ab,a,b,f;

 A2 := `list_elements/pairs`(A);
 u := table();

 for ab in A2 do 
  a,b := op(ab);
  f := `normalise_2/F`(N)({a,b})(x[{op(ab)}]);

  u[op(ab)] := combine(sqrt(2) *~ f[b]);
 od: 

 return(eval(u));
end: 

