# This is from the original version of Gemma Halliwell's thesis.
# It is probably not useful.

`build/standard_levelled_planar_tree` := proc(n::posint,num_levels::posint,u::list(posint))
 local u1,V,E,i,i1,h;

 if nops(u) <> n-1 then
  error "u should have length n-1";
 fi;

 if not(max(op(u)) < num_levels) then
  error "entries in u should be < num_levels";
 fi;
 
 u1 := [op(u),num_levels];
 V := {seq(seq([i,j],j=0..u1[i]-1),i=1..n)};
 E := {seq(seq([[i,j+1],[i,j]],j=0..u1[i]-2),i=1..n)};
 for i from 1 to n-1 do
  h := u1[i];
  i1 := i+1;
  while i1 < n and u1[i1] <= h do i1 := i1 + 1; od;
  E := {op(E),[[i1,h],[i,h-1]]};
 od;
 return [V,E];
end:

