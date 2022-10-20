######################################################################
# (n,m) shuffles, i.e. permutations of {1,..,n+m} that are increasing
# on {1,..,n} and on {n+1,..,m}

`is_element/shuffles` := (n::nonnegint,m::nonnegint) -> proc(s)
 local i;

 if not(`is_element/permutations`(n+m)(s)) then
  return false;
 fi;

 for i from 1 to n+m-1 do 
  if i <> n and s[i+1] < s[i] then
   return false;
  fi;
 od:

 return true;
end:

`is_equal/shuffles` := (n,m) -> (s,t) -> evalb(s = t);

`is_leq/shuffles` := NULL;

`from_subset/shuffles` := (n::nonnegint,m::nonnegint) -> proc(A)
 option remember;
 local X,B,i;
 
 X := {seq(i,i=1..n+m)};
 if A minus X <> {} then return FAIL; fi;
 if nops(A) <> n then return FAIL; fi;

 B := X minus A;
 return [op(sort(A)),op(sort(B))];
end:

`to_subset/shuffles` := (n::nonnegint,m::nonnegint) -> proc(s)
 local i;
 {seq(s[i],i=1..n)};
end:

`to_grid_path/shuffles` := (n::nonnegint,m::nonnegint) -> proc(s)
 local t,si,i;
 
 t := table():
 t[0] := [0,0];
 si := `inv/permutations`(n+m)(s);
 for i from 1 to n+m do
  t[i] := `if`(si[i] <= n,[1,0],[0,1]) +~ t[i-1];
 od:

 return eval(t);
end:

`from_grid_path/shuffles` := (n::nonnegint,m::nonnegint) -> proc(t)
 local A,i;

 A := select(i -> t[i][1] > t[i-1][1],{seq(i,i=1..n+m)});
 return `from_subset/shuffles`(n,m)(A);
end:

`random_element/shuffles` := (n::nonnegint,m::nonnegint) -> proc()
 local u,A,i;
 u := combinat[randperm](n+m);
 A := {seq(u[i],i=1..n)};
 return `from_subset/shuffles`(n,m)(A);
end:

`list_elements/shuffles` := proc(n::nonnegint,m::nonnegint)
 local AA;
 AA := map(A -> {op(A)},combinat[choose](n+m,n));
 return map(`from_subset/shuffles`(n,m),AA);
end:

`list_elements/inverse_shuffles` := proc(n::nonnegint,m::nonnegint)
 option remember;

 map(`inv/permutations`(n+m),`list_elements/shuffles`(n,m));
end:

`count_elements/shuffles` := (n::nonnegint,m::nonnegint) -> binomial(n+m,n);

`sgn/shuffles` := (n::nonnegint,m::nonnegint) -> proc(s)
 local i,j;
 return signum(mul(mul(s[j]-s[i],j=i+1..n+m),i=1..n+m-1));
end:
