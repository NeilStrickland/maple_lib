######################################################################

`is_element/standard_stasheff_star` := (n::posint) -> proc(t)
 local JJ,TT,J,T,u,i,j,k;
 global reason;

 if not(type(t,table)) then
  reason := [convert(procname,string),"t is not a table",t];
  return false;
 fi;

 JJ := {seq(seq({seq(k,k=i..j)},j=i..n),i=1..n)};

 if map(op,{indices(t)}) <> JJ then
  reason := [convert(procname,string),"t is not indexed by the set of intervals",t,JJ];
  return false;
 fi;

 TT := NULL;

 for J in JJ do
  u := t[J];

  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"t[J] is not in the unit interval",J,u];
   return false;
  fi;

  if (nops(J) = 1 or nops(J) = n) and u <> 1 then
   return false;
  fi;

  if u > 0 then TT := TT,J; fi;
 od;
 TT := {TT};

 if not(`is_element/trees`({seq(i,i=1..n)})(TT)) then
  reason := [convert(procname,string),"TT is not a tree",TT,reason];
  return false;
 fi;

 return true;
end;

`is_equal/standard_stasheff_star` := (n::posint) -> proc(t,u)
 local JJ,J,i,j,k;

 JJ := {seq(seq({seq(k,k=i..j)},j=i..n),i=1..n)};

 for J in JJ do
  if t[J] <> u[J] then
   return false;
  fi;
 od;
 return true;
end:

`is_leq/standard_stasheff_star` := NULL;

`random_element/standard_stasheff_star` := (n::posint) -> proc()
 local JJ,TT,T,t,i,j,k,d;

 d := 12;
 
 JJ := {seq(seq({seq(k,k=i..j)},j=i..n),i=1..n)};
 TT := `random_element/standard_stasheff_trees`(n)();
 t := table();

 for T in JJ do t[T] := 0; od;
 t[{seq(i,i=1..n)}] := 1;
 for i from 1 to n do t[{i}] := 1; od;

 for T in TT do
  if nops(T) > 1 and nops(T) < n then 
   t[T] := rand(0..d)()/d;
  fi;
 od;

 return eval(t);
end;

`list_elements/standard_stasheff_star` := NULL;
`count_elements/standard_stasheff_star` := NULL;

