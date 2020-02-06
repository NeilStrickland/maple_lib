`is_element/nat_partitions` := (total::nonnegint,num_parts::nonnegint) -> proc(u)
 return type(u,list(nonnegint)) and nops(u) = num_parts and `+`(op(u)) = total;
end:

`is_leq/nat_partitions` := NULL;

`list_elements/nat_partitions` := proc(total,num_parts)
 local L,M,i,j,m,u;

 if num_parts = 0 then 
  if total = 0 then 
   return [[]];
  else
   return [];
  fi;
 fi;

 if num_parts = 1 then return [[total]]; fi;

 L := [seq([i],i=0..total)];
 for j from 2 to num_parts-1 do
  M := NULL;
  for u in L do
   m := total - `+`(op(u));
   M := M,seq([op(u),j],j=0..m);
  od:
  L := [M];
 od:
 L := map(u -> [op(u),total - `+`(op(u))],L);

 return L;
end:

`count_elements/nat_partitions` := (total::nonnegint,num_parts::nonnegint) ->
 binomial(total+num_parts-1,total);

`random_element/nat_partitions` := (total::nonnegint,num_parts::nonnegint) -> proc()
 local X;
 if total = 0 and num_parts = 0 then
  return [];
 fi;

 X := random_subset_of({seq(i,i=1..total+num_parts-1)},num_parts-1);
 X := [0,op(sort(X)),total+num_parts];
 return [seq(X[i+1]-X[i]-1,i=1..num_parts)];
end:

`is_element/pos_partitions` := (total::nonnegint,num_parts::nonnegint) -> proc(u)
 return type(u,list(posint)) and nops(u) = num_parts and `+`(op(u)) = total;
end:

`is_leq/pos_partitions` := NULL;

`random_element/pos_partitions` := (total::nonnegint,num_parts::nonnegint) -> proc()
 local p;
 if num_parts > total then return FAIL; fi;
 p := `random_element/nat_partitions`(total - num_parts,num_parts)();
 return p +~ 1;
end:

`list_elements/pos_partitions` := proc(total,num_parts)
 map(u -> u +~ 1,`list_elements/nat_partitions`(total - num_parts,num_parts));
end:

`count_elements/pos_partitions` := (total::nonnegint,num_parts::nonnegint) ->
 binomial(total-1,num_parts-1);



