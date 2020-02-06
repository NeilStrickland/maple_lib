`is_element/young_partitions` := (k,n) -> proc(lambda)
 local i;

 if not(type(lambda,list(nonnegint))) then
  return false;
 fi;

 if nops(lambda) <> k then
  return false;
 fi;

 if k > 0 and lambda[1] > n-k then
  return false;
 fi;

 for i from 1 to k-1 do 
  if lambda[i] < lambda[i+1] then
   return false;
  fi;
 od;

 return true;
end:

`young_partition/from_set` := (n,k) -> (P) -> [seq(n-k+i-P[i],i=1..k)];

`list_elements/young_partitions` := proc(n,k)
 map(`young_partition/from_set`(n,k),combinat[choose](n,k));
end:

`random_element/young_partitions` := (n,k) -> proc()
 if k > n then return FAIL; fi;
 `young_partition/from_set`(n,k)(combinat[randcomb](n,k));
end:

`count_elements/young_partitions` := (n,k) -> binomial(n,k);

`weight/young_partitions` := (lambda) -> `+`(op(lambda)):

`length/young_partitions` := (lambda) -> nops(lambda):

`cell_dim/young_partitions` := (n,k) -> 
 k * (n - k) - `weight/young_partitions`(lambda):

`matrix/young_partitions` := (n,k) -> (lambda) -> proc(a)
 local A,P,S,u,i,j;
 A := Matrix(k,n);
 P := [seq(n-k+i-lambda[i],i=1..k)];
 S := {op(P)};
 u := 1;
 for i from 1 to k do
  for j from 1 to P[i] - 1 do
   if not(member(j,S)) then
    A[i,j] := a[u];
    u := u+1;
   fi;
  od:
  A[i,P[i]] := 1;
 od:
 return A;
end:

`giambelli_matrix/young_partitions` := proc(lambda)
 local k,f;
 k := nops(lambda);
 f := (i) -> `if`(i < 0,0,`if`(i = 0,1,c[i]));
 Matrix([seq([seq(f(lambda[i]-i+j),j=1..k)],i=1..k)]);
end:

`schur_function/young_partitions` := (lambda) ->
 Determinant(`giambelli_matrix/young_partitions`(lambda)):

