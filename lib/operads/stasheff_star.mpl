######################################################################

`eta/stasheff_star` := proc(A::set)
 if nops(A) <> 1 then return FAIL; fi;
 return [[op(A)],table([A = 1])];
end;

`gamma/stasheff_star` := (A::set,B::set) -> (p) -> proc(U,V)
 local R,S,T,r,s,t,b,n,JJ,J,pJ,J1;

 S,s := op(U);
 R := table();
 r := table();
 for b in B do 
  R[b],r[b] := op(V[b]);
 od;

 T := [seq(op(R[b]),b in S)];

 t := table();

 n := nops(T);
 JJ := {seq(seq({seq(T[k],k=i..j)},j=i..n),i=1..n)};
 for J in JJ do
  pJ := map(j -> p[j],J);
  J1 := select(j -> member(p[j],pJ),A);
  if J = J1 then
   t[J] := s[pJ];
  elif nops(pJ) = 1 then
   t[J] := r[op(pJ)][J];
  else
   t[J] := 0;
  fi;
 od:

 return [T,eval(t)];
end;

