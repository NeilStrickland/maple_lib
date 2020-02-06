######################################################################

`eta/height_functions`:= (A::set) -> `if`(nops(A)=1,table(A=0),FAIL);

######################################################################

`gamma/height_functions`:= (A::set,B::set) -> (p) -> proc(j,h)
 local k,P,phi,b0,b1,m,U,pU,b;

 k := table();
 P := `list_elements/nonempty_subsets`(A);

 phi := table();
 for b0 in B do
  m := 1;
  for b1 in B do
   if b1 <> b0 then m := min(m,j[{b0,b1}]); fi;
  od;
  phi[b0] := m;
 od;

 for U in P do
  pU := map(u -> p[u],U);
  if nops(pU) > 1 then 
   k[U] := j[pU];
  else 
   b := op(pU);
   k[U] := phi[b] * h[b][U];
  fi;
 od;

 return eval(k);
end;

######################################################################

`gamma_min/height_functions`:= (A::set,B::set) -> (p) -> proc(j,h)
 local k,P,phi,b0,b1,m,U,pU,b;

 k := table();
 P := `list_elements/nonempty_subsets`(A);

 phi := table();
 for b0 in B do
  m := 1;
  for b1 in B do
   if b1 <> b0 then m := min(m,j[{b0,b1}]); fi;
  od;
  phi[b0] := m;
 od;

 for U in P do
  pU := map(u -> p[u],U);
  if nops(pU) > 1 then 
   k[U] := j[pU];
  else 
   b := op(pU);
   k[U] := min(phi[b] , h[b][U]);
  fi;
 od;

 return eval(k);
end;
