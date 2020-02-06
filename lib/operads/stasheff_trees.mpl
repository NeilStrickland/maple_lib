######################################################################

`eta/stasheff_trees` := proc(A::set)
 if nops(A) = 1 then 
  return [`eta/ord`(A),`eta/trees`(A)];
 else
  return FAIL;
 fi;
end;

`gamma/stasheff_trees` := (A::set,B::set) -> (p) -> proc(Y,XX)
 local R,TT,SS,UUUU,b;

 R,TT := op(Y);

 SS := table();
 UUUU := table();

 for b in B do
  SS[b],UUUU[b] := op(XX[b]);
 od;

 return [`gamma/ord`(A,B)(p)(R,SS),
         `gamma/trees`(A,B)(p)(TT,UUUU)];
end;
