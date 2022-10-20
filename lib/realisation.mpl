######################################################################
# General framework for geometric realisations of finite posets.

`is_element/realisation/generic` :=
 (poset_name,el_test,leq_test) ->
proc(x)
 local pn,C,t,u,i,j,m,a,b,c;
 global reason;

 pn := cat("is_element/realisation/",poset_name);
 
 if not type(x,table) then
  reason := [pn,"x is not a table"];
  return false;
 fi;

 if map(nops,{indices(x)}) <> {1} then
  reason := [pn,"x is not a unidimensional table"];
  return false;
 fi;
 
 C := map(op,[indices(x)]);
 t := 0;
 for c in C do
  if not(el_test(c)) then
   reason := [pn,"index c is not in the poset",c];
   return false;
  fi;
  
  u := x[c];
  if not(`is_element/RR`(u) and u >= 0) then
   reason := [pn,"x[c] is not in R_+",c,x[c]];
   return false;
  fi;
  t := t+u;
 od;

 if t <> 1 then
  reason := [pn,"sum of coordinates is not equal to 1",t];
  return false;
 fi;

 m := nops(C);
 for i from 1 to m-1 do
  for j from i+1 to m do
   a := leq_test(C[i],C[j]);
   b := leq_test(C[j],C[i]);
   if not(a) and not(b) then
    reason := [pn,"incomparable indices",C[i],C[j]];
    return false;
   fi;
   if a and b then
    reason := [pn,"equivalent but unequal indices",C[i],C[j]];
    return false;
   fi;
  od;
 od;

 return true;
end;

`is_equal/realisation/generic` := 
 (poset_name,eq_test) ->
proc(x,y)
 local pn,C,D,t,u,i,j,m,a,b,c,d,dd;
 global reason;

 pn := cat("is_element/realisation/",poset_name);

 C := map(op,[indices(x)]);
 C := select(c -> x[c] > 0,C);

 D := map(op,[indices(y)]);
 D := select(d -> y[d] > 0,D);

 if nops(C) <> nops(D) then
  reason := [pn,"support sizes are different",C,D];
  return false;
 fi;
 
 for c in C do
  dd := select(d -> eq_test(c,d),D);
  if nops(dd) = 0 then
   reason := [pn,"index c in x unmatched",c];
   return false;
  fi;
  if nops(dd) > 1 then
   reason := [pn,"index c in x multiply matched",c,dd];
   return false;
  fi;
  d := dd[1];
  if x[c] <> y[d] then
   reason := [pn,"x[c] <> y[c]",c,x[c],y[c]];
   return false;
  fi;
 od;

 return true;
end;

