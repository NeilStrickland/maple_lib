######################################################################
# trees(A) is the set of trees on A
# (Section sec-trees)

`is_element/trees` := (A::set) -> proc(TT)
 local n,i,j,T,U,is_min,M;
 global reason;

 if not type(TT,set) then
  reason := [convert(procname,string),"TT is not a set",TT];
  return false;
 fi;

 n := nops(TT);
 is_min := table;
 for i from 1 to n do
  is_min[i] := true;
  T := TT[i];
  if not type(T,set) and T <> {} and T minus A = {} then
   reason := [convert(procname,string),"T is not a nonempty subset of A",T,A];
   return false;
  fi;
 od;

 # Now check nesting, and along the way, check which sets are minimal.
 for i from 1 to n do
  T := TT[i];
  for j from 1 to i-1 do
   U := TT[j];
   if T intersect U <> {} then
    if T minus U = {} then 
     is_min[j] := false;
    else
     if U minus T = {} then
      is_min[i] := false;
     else
      reason := [convert(procname,string),"T and U are neither disjoint nor nested",T,U];
      return false;
     fi;
    fi;
   fi;
  od;
 od;

 # Check that the union of the minimal sets is A.
 M := NULL;
 for i from 1 to n do
  if is_min[i] then M := M,op(TT[i]); fi;
 od;
 if A minus {M} <> {} then
  reason := [convert(procname,string),"The minimal sets do not cover A",M,A];
  return false;
 fi;

 return true;
end;

######################################################################

`is_equal/trees` := (A::set) -> (TT,UU) -> evalb(TT = UU);

######################################################################

`is_leq/trees` := (A::set) -> (TT,UU) -> evalb(TT minus UU = {});

######################################################################

`is_separated/trees` := (A::set) -> (TT) -> 
 evalb({seq({a},a in A)} minus TT = {});

######################################################################
# Suppose we have a set A, a tree TT on A, a set T in TT, and a point a that
# does not lie in A.  We can then construct a new tree on A u {a} by attaching
# a to the node T.  There are two slightly different ways to do this.  
# We can either attach a to a new node just above T, or we can attach a to 
# the node T itself.  (However, the second version is invalid if |T|=1).

`attach_to_tree` := (A::set) -> proc(TT,T,a,above_) 
 local above,CT,SCT,NCT;

 above := `if`(nargs > 3, above_, false);

 if not(`is_element/trees`(A)(TT) and
        member(T,TT) and
        not(member(a,A))) then
  return FAIL;
 fi;

 if nops(T)=1 and not(above) then 
  return FAIL;
 fi;

 # Sets that contain (or are equal to) T
 CT := select(U -> (T minus U = {}),TT);

 SCT := CT minus {T};

 # Sets that do not contain T
 NCT := TT minus CT;

 if above then
  return {{a},op(NCT),T,op(map(U -> U union {a},CT))};
 else
  return {{a},op(NCT),op(map(U -> U union {a},CT))};
 fi;
end;

######################################################################

`random_element/trees`:= (A::set) -> proc()
 local n,a,A1,T0,T1,T,above;

 # Degenerate cases for small A 
 if A={} then return {}; fi;
 if nops(A)=1 then return {A}; fi;

 # If A is not too small, we write it as {a} union A1.  Then we recursively
 # choose a random tree on A1, and attach a to it.

 n := nops(A);
 a := A[rand(1..n)()];
 A1 := A minus {a};
 if n = 2 then
  above := true;
 else
  above := evalb(rand(0..1)() = 1);
 fi;

 T0 := `random_element/trees`(A1)();
 T1 := select(U -> nops(U) > 1,T0);

 if above then
  T := T0[rand(1..nops(T0))()];
 else
  T := T1[rand(1..nops(T1))()];
 fi;

 T := `attach_to_tree`(A1)(T0,T,a,above);
 
 return T;
end;

######################################################################

`big_sets/trees` := (TT) -> select(T -> nops(T) > 1,TT);

######################################################################
# Given a tree TT, this returns a table P indexed by the non-maximal
# elements of TT, such that P[T] is the parent of T in TT.

`parent_map` := (A::set) -> proc(TT) 
 local TS,n,i,j,T,U,parent;

 # if not(`is_element/trees`(A)(TT)) then return FAIL; fi;

 TS := sort([op(TT)],(a,b) -> (nops(a) < nops(b)));
 n := nops(TS);
 parent := table();

 for i from 1 to n do
  T := TS[i];
  parent[T] := FAIL;
  for j from i+1 to n do
   U := TS[j];
   if T minus U = {} then
    parent[T] := U;
    break;
   fi;
  od;
 od;
 
 return eval(parent);
end;

######################################################################
# Given a tree TT, this returns a table C indexed by the 
# elements of TT, such that C[T] is the set of children of T in
# TT.  In particular, C[T] = {} if T is minimal.

`children_map` := (A::set) -> proc(TT)
 local parent,children,TT0,T,U;

 parent := eval(`parent_map`(A)(TT));

 children := table();
 for T in TT do 
  children[T] := {};
 od:

 TT0 := TT minus {A};

 for T in TT0 do 
  U := parent[T];
  if U <> FAIL then 
   children[U] := {op(children[U]),T};
  fi;
 od; 

 return eval(children);
end;

######################################################################

corolla := (A::set) -> {A,seq({a},a in A)};

