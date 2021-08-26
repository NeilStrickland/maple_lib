######################################################################
# Maps of finite sets

`is_element/maps` := (A::set,B::set) -> proc(p)
 local dom,cod;
 global reason;

 if not(type(p,table)) then
  reason := [convert(procname,string),"not table"];
  return false;
 fi;

 # Note, if p has indices 5, 6 and 7 then indices(p) will return 
 # [5],[6],[7] (an unbracketed list with each individual entry in
 # square brackets).  The construct map(op,{indices(p)}) gives 
 # {5,6,7} instead.
 dom := map(op,{indices(p)});
 if dom <> A then
  reason := [convert(procname,string),"wrong domain",dom,A];
  return false;
 fi;

 # Similarly, if p[5]=55 and p[6]=66 and p[7]=77 then entries(p)
 # is [55],[66],[77] but map(op,{entries(p)}) is {55,66,77}.
 cod := map(op,{entries(p)});
 if cod minus B <> {} then
  reason := [convert(procname,string),"wrong codomain",cod,B];
  return false;
 fi;

 return true;
end;

`is_equal/maps` := (A::set,B::set) -> proc(p,q)
 local a;
 global reason;

 for a in A do 
  if p[a] <> q[a] then
   reason := [convert(procname,string),"different value",a,p[a],q[a]];
   return false;
  fi; 
 od;

 return true;
end;

`is_leq/maps` := NULL;

`random_element/maps` := (A::set,B::set) -> proc()
 local p,n,r,a;

 p := table();
 if B = {} then
  if A = {} then
   return eval(p);
  else
   return FAIL;
  fi;
 fi;

 # nops(B) gives the number of operands in B.  Here B is supposed
 # to be a set, so the operands are just the elements.
 n := nops(B);

 # Note that the line below defines r to be a function such that each
 # invocation of r() will return a new random number in the range 
 # {1,...,n}.
 r := rand(1..n);

 for a in A do p[a] := B[r()]; od;

 return eval(p);
end;

# To list the maps from A to B, we let a be the first element in A,
# and put A0 = A \ {a}.  By induction we can enumerate all the maps
# p0 : A0 -> B, and we generate all possible extensions of p0 by
# sending a to each possible element of B.

`list_elements/maps` := proc(A::set,B::set)
 local A0,a,b,M0,M,p0,p;

 # The unique map from the empty set to B is represented by a 
 # table with no entries; this starts the induction.
 if A = {} then
  return [table()];
 fi;

 A0 := sort([op(A)]);
 a := A0[1];
 A0 := {op(2..-1,A0)};
 M0 := `list_elements/maps`(A0,B);
 M := [];

 for b in B do
  for p0 in M0 do
   p := copy(p0);
   p[a] := b;

   # The next line is the standard way to append an element to the
   # list M.  We use op() to strip off the square brackets, and then
   # put them back in with the new element eval(p) inside.  The 
   # reason for eval(p) instead of p is technical and will not be 
   # explained here, except to say that p is a table and it is 
   # often good to apply eval() to tables if they are going to be
   # returned as values of functions or otherwise passed around.
   M := [op(M),eval(p)];
  od;
 od;

 return M;
end;

`count_elements/maps` := (A::set,B::set) -> nops(B) ^ nops(A);

# fibres(A,B)(p) assumes that p is a function from A to B, and
# returns a table indexed by the elements of B, whose entries 
# are the fibres p^{-1}{b}.

fibres := (A::set,B::set) -> proc(p)
 local F,a,b;

 F := table();
 for b in B do F[b] := {}; od;
 for a in A do F[p[a]] := {op(F[p[a]]),a}; od;
 for b in B do F[b] := sort(F[b]); od;
 
 return eval(F);
end;

# `id/maps`(A) is the identity map A -> A
`id/maps` := proc(A::set) local a; table({seq(a=a,a in A)}); end:

# `compose/maps`(A,B,C)(p,q) assumes that p : A -> B and q : B -> C,
# and it returns the composite q o p : A -> C.
`compose/maps` := (A::set,B::set,C::set) -> proc(p,q) local a;
  table({seq(a = q[p[a]],a in A)}); end:

