######################################################################
# epi(A,B) is the set of surjective maps from A to B

`is_element/epi` := (A::set,B::set) -> proc(p)
 local a,b,hit;
 global reason;

 if not `is_element/maps`(A,B)(p) then
  reason := [convert(procname,string),"p is not a map from A to B",p,A,B,reason];
  return false;
 fi;

 hit := table();
 for b in B do hit[b] := false; od;
 for a in A do hit[p[a]] := true; od;
 for b in B do if not hit[b] then
  reason := [convert(procname,string),"b is not hit",b];
  return false;
 fi; od;
 return true;
end;

`is_equal/epi` := (A::set,B::set) -> proc(p,q)
 local a;
 global reason;

 for a in A do 
  if p[a] <> q[a] then
   reason := [convert(procname,string),"p[a] <> q[a]",a,p[a],q[a]];
   return false;
  fi; 
 od;

 return true;
end;

`is_leq/epi` := NULL;

`random_element/epi` := (A::set,B::set) -> proc()
 local p,m,n,A0,r,i;

 n := nops(A);
 m := nops(B);
 if m > n then return FAIL; fi;

 p := table();
 A0 := combinat[randperm]([op(A)]);

 for i from 1 to m do p[A0[i]] := B[i]; od;

 r := rand(1..m);

 for i from m+1 to n do p[A0[i]] := B[r()]; od;

 return eval(p);
end;

`list_elements/epi` := proc(A::set,B::set)
 local n,m,B0,b,E,E0,k,CC,C,c,p0,p;

 n := nops(A);
 m := nops(B);

 if n < m then return []; fi;
 if m = 0 then
  if n = 0 then 
   return [table()];
  else 
   return [];
  fi;
 fi;

 B0 := sort(B);
 b := B0[1];
 B0 := {op(2..-1,B0)};

 E := [];

 for k from 1 to n-m+1 do
  CC := combinat[choose](A,k);
  for C in CC do
   E0 := `list_elements/epi`(A minus C,B0);
   for p0 in E0 do
    p := copy(p0);
    for c in C do p[c] := b; od;
    E := [op(E),eval(p)];
   od;
  od;
 od;

 return E;
end;

`count_elements/epi` := (A::set,B::set) -> Stirling2(nops(A),nops(B)) * nops(B)!;