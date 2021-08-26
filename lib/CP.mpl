######################################################################
# CP(N) is the projective space CP^N

`is_element/CP` := (N::posint) -> proc(x,t := constant)
 if not (type(x,[t $ (N+1)])) then
  return false;
 fi;
 
 if simplify(x) = [0$(N+1)] then 
  return false;
 fi;

 return true;
end:

`is_equal/CP` := (N::posint) -> proc(x,y)
 local i,j;
 for i from 1 to N do
  for j from i+1 to N do
   if simplify(x[i] * y[j] - x[j] * y[i]) <> 0 then
    return false;
   fi;
  od;
 od; 

 return true;
end:

`is_leq/CP` := NULL;

`random_element/CP` := (N::posint) -> proc() local i; [seq(`random_element/CC`(),i=1..N+1)] end;

`list_elements/CP` := NULL;
`count_elements/CP` := NULL;