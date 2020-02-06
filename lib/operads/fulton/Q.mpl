######################################################################

`is_element/Q` := (A::set) -> proc(t)
 local A3,abc,a,b,c,r2;
 global reason;

 if not(type(t,table)) then
  reason := [convert(procname,string),"t is not a table"];
  return false;
 fi;

 A3 := `list_elements/triples`(A);

 if {indices(t)} <> {op(A3)} then
  reason := [convert(procname,string),"t is not indexed by triples in A",t,A3];
  return false;
 fi;

 for abc in A3 do
  a,b,c := op(abc);
  if not(`is_element/RR`(t[a,b,c])) then
   reason := [convert(procname,string),"t[a,b,c] is not in R",a,b,c,t[a,b,c]];
   return false;
  fi;
  if not(is(t[a,b,c] >= 0)) then return false; fi;
 od;

 for abc in A3 do
  a,b,c := op(abc);
  if simplify(t[a,b,c] - t[b,a,c]) <> 0 then
   reason := [convert(procname,string),"t[a,b,c] <> t[b,a,c]",a,b,c,t[a,b,c],t[b,a,c]];
   return false;
  fi; 
  r2 := simplify(t[a,b,c]^2 + t[b,c,a]^2 + t[c,a,b]^2);
  if simplify(r2-1) <> 0 then
   reason := [convert(procname,string),"t is not normalised on {a,b,c}",a,b,c,r2];
   return false;
  fi; 
 od;

 return true;
end:

`psi/Fbar/Q` := (N::posint) -> (A::set) -> proc(x)
 local A3,t,abc,a,b,c,f,g;

 A3 := `list_elements/triples`(A);
 t := table();

 for abc in A3 do 
  a,b,c := op(abc);
  f := `normalise_2/F`(N)({a,b,c})(x[{a,b,c}]);
  g := `normalise_2/F`(N)({a,b})(x[{a,b}]);
  t[a,b,c] := combine(simplify(`dot/R`(N)(f[b] -~ f[a],g[b])*sqrt(2/3)));
 od;

 return(eval(t));
end:

