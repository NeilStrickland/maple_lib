######################################################################
# Partitions of the set {1,...,n} into intervals

`is_element/interval_partitions` := (n::posint) -> proc(pi)
 local A,U;
 global reason;

 A := {seq(i,i=1..n)};

 if not(`is_element/partitions`(A)(pi)) then
  reason := [convert(procname,string),"pi is not a partition",pi,reason];
  return false;
 fi;

 for U in pi do
  if not(`is_element/posint_intervals`(U)) then
   reason := [convert(procname,string),"U is not a posint interval",U];
   return false;
  fi;
 od;

 return true;
end:

`is_equal/interval_partitions` := (n::posint) -> proc(pi,rho)
 local A;

 A := {seq(i,i=1..n)};
 return `is_equal/partitions`(A)(pi,rho);
end:

`is_leq/interval_partitions` := (n::posint) -> proc(pi,rho)
 local A;

 A := {seq(i,i=1..n)};
 return `is_leq/partitions`(A)(pi,rho);
end:

# Given an integer n > 0 and a subset C of {1/2,3/2,...,(2n-1)/2}, this
# returns the partition of {1,...,n} obtained by cutting at the points
# of C.

`cut_partition` := proc(n::posint,C)
 local m,C0,C1;

 m := 1 + nops(C);
 C0 := sort([1,op(map(c->c+1/2,C))]);
 C1 := sort([op(map(c->c-1/2,C)),n]);
 return {seq({seq(j,j=C0[i]..C1[i])},i=1..m)};
end;

`random_element/interval_partitions` := (n::posint) -> proc()
 local C;

 C := `random_element/subsets`({seq(i+1/2,i=1..n-1)})();
 return cut_partition(n,C);
end;

`list_elements/interval_partitions` := proc(n)
 local G,P;

 G := {seq(i+1/2,i=1..n-1)};
 P := `list_elements/subsets`(G);
 return map(C -> cut_partition(n,C),P);
end;

`count_elements/interval_partitions` := (n) -> 2^(n-1);

