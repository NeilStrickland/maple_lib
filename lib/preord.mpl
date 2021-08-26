######################################################################

`is_element/preord` := (A::set) -> proc(R)
 global reason;

 if not `is_element/autorel`(A)(R) then
  reason := [convert(procname,string),"R is not a relation on A",R,A,reason];
  return false;
 fi;

 if not(`is_reflexive/autorel`(A)(R)) then
  reason := [convert(procname,string),"R is not reflexive",R];
  return false;
 fi;
 
 if not(`is_transitive/autorel`(A)(R)) then
  reason := [convert(procname,string),"R is not transitive",R];
  return false;
 fi;
 
 return true;
end;

######################################################################

`is_equal/preord`     := eval(`is_equal/autorel`);
`is_separated/preord` := eval(`is_separated/autorel`);

# We order the set of preorders by reverse inclusion, so that 
# separated preorders are maximal.

`is_leq/preord`       := (A::set) -> proc(R,S)
 evalb(S minus R = {});
end;
 

`op/preord` := eval(`op/autorel`);

######################################################################

`random_element/preord` := (A::set) -> proc(R)
 local pi,n,r,i,a,b,N,RN,A2,RA;

 pi := `random_element/partitions`(A)();
 n := nops(pi);
 r := table();
 for i from 1 to n do
  for a in pi[i] do
   r[a] := i;
  od:
 od:
 N := {seq(i,i=1..n)};
 RN := `random_element/partord`(N)();
 A2 := {seq(seq([a,b],b in A),a in A)};
 RA := select(u -> member([r[u[1]],r[u[2]]],RN),A2);

 return RA;
end:

######################################################################

`is_total/preord` := (A::set) -> proc(R)
 local U,a,b;

 U := R union `op/preord`(A)(R);
 U := {seq(seq([a,b],b in A),a in A)} minus U;

 return evalb(U = {}); 
end;

######################################################################

`strictify/preord` := (A::set) -> proc(R)
 return R minus `op/preord`(A)(R);
end:

######################################################################

`res/preord` := (A::set,B::set) -> (R) ->
 select(xy -> member(xy[1],B) and member(xy[2],B),R);

######################################################################

`block_partition/preord` := (A::set) -> proc(R)
 local E,pi,X,x,B;

 E := R intersect map(ab -> [ab[2],ab[1]],R);
 pi := NULL;
 X := A;

 while X <> {} do
  x := X[1];
  B := map(ab -> ab[2],select(ab -> ab[1] = x,E));
  pi := pi,B;
  X := X minus B;
 od:

 pi := {pi};

 return pi;
end:

######################################################################
# Note that the function below is not actually a rank function, but
# it is an ingredient in certain rank functions to be defined 
# elsewhere.

`rank/preord` := (A::set) -> proc(R)
 nops(`block_partition/preord`(A)(R));
end:

######################################################################

`bump/preord` := (A::set) -> proc(R)
 local pi,B,a,b,B0,R0;

 pi := `block_partition/preord`(A)(R);

 for B in pi do 
  if nops(B) > 1 then
   a := B[1];
   B0 := B minus {a};
   R0 := R minus {seq([b,a],b in B0)};
   return R0;
  fi;
 od;

 return FAIL;
end:

######################################################################

`rank_table/preord` := (A::set) -> proc(R)
 local pi,pi0,a,b,r,k,B;
 
 pi := `block_partition/preord`(A)(R);
 pi0 := map(B -> B[1],pi);
 r := table():
 for B in pi do
  k := nops(select(a -> member([a,B[1]],R),pi0)) - 1;
  for b in B do r[b] := k; od;
 od;

 return eval(r);
end;

######################################################################

`separated_quotient/preord` := (A::set) -> proc(R)
 local A0,R0,a0,b0;

 A0 := `block_partition/preord`(A)(R);
 R0 := NULL;
 for a0 in A0 do
  for b0 in A0 do
   if member([a0[1],b0[1]],R) then
    R0 := R0,[a0,b0];
   fi;
  od;
 od;
 R0 := {R0};

 return [A0,R0];
end: 

######################################################################

`preord_is_leq` := (A::set) -> (R) -> (a,b) -> member([a,b],R);

######################################################################

`preord_is_equiv` := (A::set) -> (R) -> (a,b) ->
  member([a,b],R) and member([b,a],R);

######################################################################

`preord_is_less` := (A::set) -> (R) -> (a,b) ->
  member([a,b],R) and not(member([b,a],R));


