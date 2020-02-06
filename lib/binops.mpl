######################################################################
# Binary operations on finite sets

`is_element/binops` := (A::set,B::set,C::set) -> proc(p)
 local AB,dom,cod;
 global reason;

 if not(type(p,table)) then
  reason := [convert(procname,string),"not table"];
  return false;
 fi;

 AB := {seq(seq([a,b],b in B),a in A)};

 if {indices(p)} <> AB then
  reason := [convert(procname,string),"wrong domain",{indices(p)},AB];
  return false;
 fi;

 cod := map(op,{entries(p)});
 if cod minus C <> {} then
  reason := [convert(procname,string),"wrong codomain",cod,C];
  return false;
 fi;

 return true;
end;

`is_equal/binops` := (A::set,B::set,C::set) -> proc(p,q)
 local a,b;
 global reason;

 for a in A do 
  for b in B do
   if p[a,b] <> q[a,b] then
    reason := [convert(procname,string),"different value",a,b,p[a,b],q[a,b]];
    return false;
   fi;
  od;
 od;

 return true;
end;

`is_leq/binops` := NULL;

`random_element/binops` := (A::set,B::set,C::set) -> proc()
 local p,n,r,a,b;

 p := table();
 if B = {} then
  if A = {} then
   return eval(p);
  else
   return FAIL;
  fi;
 fi;

 n := nops(C);

 r := rand(1..n);

 for a in A do
  for b in B do 
   p[a,b] := C[r()];
  od;
 od;
 
 return eval(p);
end;

`list_elements/binops` := proc(A::set,B::set,C::set)
 local nA,nB,nC,J,L,i;

 nA := nops(A);
 nB := nops(B);
 nC := nops(C);
 J := [seq(seq([A[i],B[j]],j=1..nB),i=1..nA)];
 L := [[]];
 for i from 1 to nA*nB do
  L := [seq(seq([op(u),j],j=1..nC),u in L)];
 od:

 L := map(u -> table([seq(op(J[k])=C[u[k]],k=1..nA*nB)]),L);
 return L;
end;

`count_elements/binops` := (A::set,B::set,C::set) -> nops(C) ^ (nops(A)*nops(B));

`is_associative/binops` := (A::set) -> proc(m)
 local a,b,c;
 for a in A do 
  for b in A do
   for c in A do
    if m[a,m[b,c]] <> m[m[a,b],c] then
     return false;
    fi;
   od;
  od;
 od;
 return true;
end:

`is_commutative/binops` := (A::set) -> proc(m)
 local a,b;
 for a in A do 
  for b in A do
   if m[a,b] <> m[b,a] then
    return false;
   fi;
  od;
 od;
 return true;
end:

`is_left_proj/binops` := (A::set) -> proc(m)
 local a,b;
 for a in A do 
  for b in A do
   if m[a,b] <> a then
    return false;
   fi;
  od;
 od;
 return true;
end:

`is_right_proj/binops` := (A::set) -> proc(m)
 local a,b;
 for a in A do 
  for b in A do
   if m[a,b] <> b then
    return false;
   fi;
  od;
 od;
 return true;
end:

`is_idempotent/binops` := (A::set) -> proc(m)
 local a;
 for a in A do 
  if m[a,a] <> a then
   return false;
  fi;
 od;
 return true;
end:

`is_left_neutral/binops` := (A::set) -> proc(m,e)
 local a;

 if not(member(e,A)) then return false; fi;
 for a in A do 
  if m[e,a] <> a then return false; fi;
 od: 
 return true;
end:

`is_right_neutral/binops` := (A::set) -> proc(m,e)
 local a;

 if not(member(e,A)) then return false; fi;
 for a in A do 
  if m[a,e] <> a then return false; fi;
 od: 
 return true;
end:

`is_neutral/binops` := (A::set) -> proc(m,e)
 return `is_left_neutral/binops`(A)(m,e) and
        `is_right_neutral/binops`(A)(m,e);
end:

`has_left_neutral/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_left_neutral/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:

`has_right_neutral/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_right_neutral/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:

`has_neutral/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_neutral/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:

`is_left_absorbing/binops` := (A::set) -> proc(m,e)
 local a;

 if not(member(e,A)) then return false; fi;
 for a in A do 
  if m[e,a] <> e then return false; fi;
 od: 
 return true;
end:

`is_right_absorbing/binops` := (A::set) -> proc(m,e)
 local a;

 if not(member(e,A)) then return false; fi;
 for a in A do 
  if m[a,e] <> e then return false; fi;
 od: 
 return true;
end:

`is_absorbing/binops` := (A::set) -> proc(m,e)
 return `is_left_absorbing/binops`(A)(m,e) and
        `is_right_absorbing/binops`(A)(m,e);
end:

`has_left_absorbing/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_left_absorbing/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:

`has_right_absorbing/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_right_absorbing/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:

`has_absorbing/binops` := (A::set) -> proc(m)
 local e;

 for e in A do
  if `is_absorbing/binops`(A)(m,e) then
   return true;
  fi;
 od:
 return false;
end:



