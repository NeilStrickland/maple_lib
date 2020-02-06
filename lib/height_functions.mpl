######################################################################

`is_element/height_functions` := (A::set) -> proc(h)
 local P,U,V,a,u;
 global reason;

 if not(type(h,table)) then
  reason := [convert(procname,string),"h is not a table",h];
  return false;
 fi;

 P := {op(`list_elements/nonempty_subsets`(A))};
 if map(op,{indices(h)}) <> P then
  reason := [convert(procname,string),"h is not indexed by the nonempty subsets of A",h,A];
  return false;
 fi;

 for a in A do if h[{a}] <> 0 then
  reason := [convert(procname,string),"h({a}) <> 0",h,a];
  return false;
 fi; od;

 for U in P do 
  u := h[U];
  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"h(U) is not in the unit interval",U,u];
   return false;
  fi;
 od;

 for U in P do
  for V in P do
   if U intersect V <> {} and 
      h[U union V] <> max(h[U],h[V]) then
    reason := [convert(procname,string),"h(U u V) <> max(h(U),h(V))",U,V,h[U],h[V],h[U union V]];
    return false;
   fi;
  od;
 od;

 return true;
end;

######################################################################

`is_equal/height_functions` := (A::set) -> proc(h1,h2)
 local P,U;
 P := `list_elements/nonempty_subsets`(A);
 for U in P do
  if h1[U] <> h2[U] then return false; fi;
 od;
 return true;
end;

######################################################################

`is_leq/height_functions` := NULL;

`list_elements/height_functions` := NULL;
`count_elements/height_functions` := NULL;

######################################################################

`is_critical/height_functions` := (A::set) -> proc(h,U)
 local V,a;

 V := A minus U;

 if V = {} then return evalb(h[A] < 1); fi;

 for a in V do
  if h[U union {a}] = h[U] then return false; fi;
 od;

 return true;
end;

######################################################################

`critical_tree/height_functions` := (A::set) -> proc(h)
 local P;

 P := `list_elements/nonempty_subsets`(A);

 return {op(select(U ->`is_critical/height_functions`(A)(h,U),P))};
end;

######################################################################

`theta/partitions/height_functions` := (A::set) -> proc(pi)
 local h,P,T,B,Q;

 h := table();
 P := `list_elements/nonempty_subsets`(A);
 for T in P do h[T] := 1; od;
 for B in pi do
  Q := `list_elements/nonempty_subsets`(B);
  for T in Q do h[T] := 0; od;
 od;

 return eval(h);
end;

######################################################################

`theta/realisation/partitions/height_functions` := (A::set) -> proc(x)
 local P,T,C,pi,t,k,h;

 h := table();
 P := `list_elements/nonempty_subsets`(A);
 for T in P do h[T] := 0; od;

 C := map(op,[indices(x)]);

 for pi in C do
  t := x[pi];
  k := `theta/partitions`(A)(pi);
  for T in P do
   h[T] := h[T] + t * k[T];
  od;
 od;

 return eval(h);
end:

######################################################################

`theta_inv/realisation/partitions/height_functions` := (A::set) -> proc(h)
 local TT,TTT,S,r,s,t,x,U,X,Y,pi,a,m,i;
 
 TT := `critical_tree/height_functions`(A)(h);
 S := map(T -> h[T],TT) minus {1};
 r := nops(S) - 1;
 s := table();
 s[-1] := 1;
 for i from 0 to r do s[i] := S[r+1-i]; od;
 TTT := table();
 x := table();
 for i from 0 to r do
  TTT[i] := select(U -> h[U] <= s[i],TT);
  X := TTT[i];
  pi[i] := {};
  while X <> {} do
   a := X[1][1];
   Y := select(T -> member(a,T),X);
   m := max(map(nops,Y));
   U := select(T -> nops(T) = m,Y)[1];
   pi[i] := {op(pi[i]),U};
   X := X minus Y;
  od;
  x[pi[i]] := s[i-1] - s[i]; 
 od;

 return eval(x);
end:
