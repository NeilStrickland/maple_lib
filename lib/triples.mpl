######################################################################
# triples(A) is the set of all distinct triples (a,b,c) in A^3

`is_element/triples` := (A::set) -> proc(abc)
 type(abc,list) and nops(abc) = 3 and
 member(abc[1],A) and member(abc[2],A) and member(abc[3],A) and
 abc[1] <> abc[2] and abc[1] <> abc[3] and abc[2] <> abc[3];
end;

`is_equal/triples` := (A::set) -> (abc,def) -> evalb(abc = def):

`is_leq/triples` := NULL;

`random_element/triples` := (A::set) -> proc()
 local n,r,i,j,k,abc;
 n := nops(A);

 if n < 3 then return FAIL; fi;

 abc := [];

 while nops({op(abc)}) < 3 do 
  i := rand(1..n)(); 
  j := rand(1..n)();
  k := rand(1..n)();
  abc := [A[i],A[j],A[k]];
 od;

 return abc;
end;

`list_elements/triples` := proc(A::set)
 local n,L,i,j,k;

 n := nops(A);
 L := NULL;

 for i from 1 to n do 
  for j from 1 to n do 
   for k from 1 to n do 
    if i <> j and i <> k and j <> k then
     L := L,[A[i],A[j],A[k]];
    fi;
   od;
  od;
 od;

 return [L];
end:

`count_elements/triples` := (A::set) ->
 nops(A) * (nops(A) - 1) * (nops(A) - 2);
 