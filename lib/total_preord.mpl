`is_element/total_preord` := (A::set) -> proc(R)
 local AA,a,b,ab,U;

 global reason;

 AA := [seq(seq([a,b],b in A),a in A)];

 if not(`is_element/preord`(A)(R)) then
  reason := [convert(procname,string),"R is not a preorder",R,reason];
  return false;
 fi;

 if not(`is_total/preord`(A)(R)) then
  reason := [convert(procname,string),"R is not a total preorder on A",R,A];
  return false;
 fi;

 return true;
end;

`is_equal/total_preord` := (A::set) -> (R1,R2) -> `is_equal/preord`(A)(R1,R2);
`is_leq/total_preord`   := (A::set) -> (R1,R2) -> `is_leq/preord`(A)(R1,R2);

######################################################################

`build/total_preord` := (A::set) -> proc(pi)
 local m,r,i,a,b,R;
 
 m := nops(pi);
 r := table();
 for i from 1 to m do
  for a in pi[i] do
   r[a] := i;
  od;
 od;

 R := NULL;
 for a in A do
  for b in A do
   if r[a] <= r[b] then R := R,[a,b]; fi;
  od;
 od;
 R := {R};

 return R;
end;

######################################################################

`random_element/total_preord` := (A::set) -> proc()
 local pi,pi0,pi1,m,r,i,a,b,R;

 pi := `random_element/partitions`(A)();
 pi0 := map(u -> sort([op(u)]),pi);
 pi0 := sort([op(pi0)]);
 pi1 := combinat[randperm](pi0);
 return `build/total_preord`(A)(pi1);
end;

######################################################################

`list_elements/total_preord` := proc(A::set)
 local PI,pi,pi0,pi1,L;

 PI := `list_elements/partitions`(A);
 L := NULL;
 for pi in PI do
  pi0 := map(u -> sort([op(u)]),pi);
  pi0 := sort([op(pi0)]);
  for pi1 in combinat[permute](pi0) do
   L := L,`build/total_preord`(A)(pi1);
  od;
 od;
 L := [L];
 return L;
end;

######################################################################

`count_elements/total_preord` := proc(A::set)
 local n,k;
 n := nops(A);
 add(k! * Stirling2(n,k),k=1..n);
end;
