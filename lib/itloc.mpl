`is_element/itloc/I` := (n::nonnegint) -> (i) ->
 type(i,nonnegint) and i < n:

`list_elements/itloc/I` := (n::nonnegint) -> [seq(i,i=0..n-1)]:

######################################################################

`is_element/itloc/P` := (n::nonnegint) -> (A) -> 
 type(A,set(nonnegint)) and (nops(A) = 0 or max(0,op(A)) < n):

`list_elements/itloc/P` := (n::nonnegint) ->
 [op(combinat[powerset]({seq(i,i=0..n-1)}))];

`is_leq/itloc/P` := (n::nonnegint) -> (A,B) -> evalb (A minus B = {});

`bot/itloc/P` := (n::nonnegint) -> {};

`top/itloc/P` := (n::nonnegint) -> {seq(i,i=0..n-1)};

`sup/itloc/P` := (n::nonnegint) -> (A,B) -> A union B;

`inf/itloc/P` := (n::nonnegint) -> (A,B) -> A intersect B;

`angle/itloc/P` := (n::nonnegint) -> (A,B) ->
 (A = {} or B = {} or max(op(A)) <= min(op(B)));

######################################################################

`is_element/itloc/Q` := (n::nonnegint) -> proc(U)
 local N,A,b;

 if not type(U,set(set(nonnegint))) then
  return false;
 fi;

 if n = 0 then
  return evalb(U minus {{}} = {});
 fi;

 if max(0,op(map(op,U))) >= n then
  return false;
 fi;

 N := `list_elements/itloc/I`(n);
 
 for A in U do
  for b in N minus A do
   if not(member(A union {b},U)) then
    return false;
   fi;
  od;
 od;

 return true;
end:

`is_leq/itloc/Q` := (n::nonnegint) -> (U,V) -> evalb (V minus U = {});

`itloc/u` := (n::nonnegint) -> proc (A::set(nonnegint))
 local BB;
 
 BB := `list_elements/itloc`(n) minus A;

 return map(B -> A union B,BB);
end:

`bot/itloc/Q` := (n::nonnegint) -> `itloc/u`(n)({});

`top/itloc/Q` := (n::nonnegint) -> {};

`omul/itloc/Q` := (n::nonnegint) -> proc(U,V)
 local UV;

 UV := {seq(seq([A,B],B in V),A in U)};

 UV := select(AB -> `angle/itloc/P`(n)(op(AB)),UV);

 return UV;
end:

`mul/itloc/Q` := (n::nonnegint) -> (U,V) ->
 map(AB -> AB[1] union AB[2],`omul/itloc/Q`(U,V));

######################################################################

`is_element/itloc/M` := (n::nonnegint) -> (AB) -> 
 type(AB,list) and nops(AB) = 2 and
  `is_element/itloc/P`(n)(AB[1]) and 
  `is_element/itloc/P`(n)(AB[2]) and
  `itloc/angle`(n)(op(AB));

`list_elements/itloc/M` := proc(n::nonnegint)
 local P,Q,i;
 
 P := `list_elements/itloc/P`(n);
 Q := table();
 for i from 0 to n do
  Q[i] := combinat[powerset]({seq(j,j=i..n-1)});
 end:
 return [seq(seq([A,B],B in Q[max(0,op(A))]),A in P)];
end:

`is_leq/itloc/M` := (n::nonnegint) -> (AB0,AB1) ->
 evalb (`is_leq/itloc/P`(n)(AB0[1],AB1[1]) and
        `is_leq/itloc/P`(n)(AB0[2],AB1[2]));

`bot/itloc/M` := (n::nonnegint) -> [{},{}];

`inf/itloc/M` := (n::nonnegint) -> (AB0,AB1) ->
 [AB0[1] intersect AB1[1],AB0[2] intersect AB1[2]];

`zeta/itloc`  := (n::nonnegint) -> B -> [{},B];
`xi/itloc`    := (n::nonnegint) -> A -> [A,{}];

`sigma/itloc` := (n::nonnegint) -> AB -> AB[1] union AB[2];

`alpha/itloc` := (n::nonnegint) -> (i) -> (AB) ->
 [select(a -> a < i,AB[1]), select(a -> a >= i,AB[1]) union AB[2]];

`beta/itloc`  := (n::nonnegint) -> (i) -> (AB) ->
 [select(a -> a <= i,AB[1]), select(a -> a >= i,AB[1]) union AB[2]];

`gamma/itloc` := (n::nonnegint) -> (i) -> (AB) ->
 [AB[1] union select(b -> b < i,AB[2]), select(b -> b >= i,AB[2])];

`delta/itloc` := (n::nonnegint) -> (i) -> (AB) ->
 [AB[1] union select(b -> b <= i,AB[2]), select(b -> b >= i,AB[2])];

######################################################################

`is_element/itloc/L` := (n::nonnegint) -> proc(U)
 local N,AB,A,B,a,b,A1,B1,i,j;

 if not type(U,set(list(set(nonnegint)))) then
  return false;
 fi;

 N := `list_elements/itloc/I`(n);
 
 for AB in U do
  if not(`is_element/itloc/M`(n)(AB)) then
   return false;
  fi;
 od;
 
 for AB in U do
  A,B = op(AB);
  a := max(0,op(A));
  b := min(n-1,op(B));
  A1 := {seq(i,i=0..b)} minus A;
  B1 := {seq(i,i=a..n-1)} minus B;
  for i in A1 do
   if not(member([A union {i},B]),U) then return false; fi;
  od;
  for j in B1 do
   if not(member([A,B union {j}]),U) then return false; fi;
  od;
 od;

 return true;
end:

`is_leq/itloc/L` := (n::nonnegint) -> (U,V) -> evalb (V minus U = {})

`itloc/v` := (n::nonnegint) -> proc (AB::[set(nonnegint),set(nonnegint)])
 local a,b,A,A1,A2,A3,B,B1,L;

 A,B = op(AB);
 b := min(n-1,op(B));
 A1 := {seq(i,i=0..b)} minus A;

 L := NULL;
 for A2 in combinat[powerset](A1) do
  A3 := A union A2;
  a := max(0,op(A3));
  B1 := {seq(j,j=a..n-1)} minus B;
  L := L,seq([A3,B union B2],B2 in combinat[powerset](B1));
 od:
 return {L};
end:


