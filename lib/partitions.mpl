######################################################################
# partitions(A) is the set of all partitions of A
# (Section sec-partitions)

# Partitions are represented as nonempty sets of nonempty subsets, so 
# {{1,2},{3},{4,5}} is an element of partitions({1,2,3,4,5}).

`is_element/partitions` := (A::set) -> proc(pi)
 local n,T,U;
 global reason;

 if not type(pi,set) then
  reason := [convert(procname,string),"pi is not a set",pi];
  return false;
 fi;

 n := nops(pi);
 if n = 0 then
  reason := [convert(procname,string),"pi is empty"];
  return false;
 fi;

 T := {};

 for U in pi do
  if U = {} then
   reason := [convert(procname,string),"pi contaisn the empty set",pi];
   return false;
  fi;

  if U minus A <> {} then
   reason := [convert(procname,string),"U is not contained in A",U,A];
   return false;
  fi;

  if T intersect U <> {} then
   reason := [convert(procname,string),"sets in pi are not disjoint",U,T];
   return false;
  fi;

  T := T union U;
 od;

 if A minus T <> {} then
  reason := [convert(procname,string),"sets in pi do not cover A",T,A];
  return false;
 fi;

 return true; 
end;

######################################################################

`is_equal/partitions` := (A::set) -> (pi,rho) -> evalb(pi = rho):

######################################################################

`is_leq/partitions` := (A::set) -> proc(pi,rho)
 local T,U,ok;
 global reason;

 for T in rho do
  ok := false;
  for U in pi do
   if T minus U = {} then
    ok := true;
    break;
   fi;
  od;

  if not ok then
   reason := [convert(procname,string),"T is not contained in any block of pi",T,pi];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`random_element/partitions` := (A::set) -> proc()
 local n,m,r,t,i,a,pi;

 if A = {} then return FAIL; fi;

 n := nops(A);
 m := rand(1..n)();
 r := rand(1..m);
 t := table();
 for i from 1 to m do t[i] := NULL; od;
 for a in A do 
  i := r();
  t[i] := t[i],a;
 od:

 pi := NULL;
 for i from 1 to m do
  if t[i] <> NULL then pi := pi,{t[i]}; fi;
 od;

 pi := {pi};

 return pi;
end;

######################################################################

`list_elements/partitions` := proc(A::set)
 local n,a,A0,B0,B,C,S,P,Q,rho,pi;

 n := nops(A);
 if n = 0 then return {}; fi;
 if n = 1 then return {{A}}; fi; 

 A0 := sort([op(A)]);
 a := A0[1];
 A0 := {op(2..-1,A0)};
 P := {A};
 S := `list_elements/subsets`(A0);

 for B0 in S do
  B := {a,op(B0)};
  Q := `list_elements/partitions`(A minus B);
  for rho in Q do
   pi := {B,op(rho)};
   P := P,pi;
  od;
 od;

 P := [P];
 return P;
end;

######################################################################

`count_elements/partitions` := (A::set) -> combinat[bell](nops(A));

`top/partitions` := (A::set) -> `if`(A = {},FAIL,map(a -> {a},A));

`bot/partitions` := (A::set) -> `if`(A = {},FAIL,{A});