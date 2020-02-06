######################################################################

`is_element/tree_height_functions` := (A::set) -> (TT) -> proc(h)
 local P,U,V,a,u,is_minimal;
 global reason;

 if not(type(h,table)) then
  reason := [convert(procname,string),"h is not a table",h];
  return false;
 fi;

 if map(op,{indices(h)}) <> TT then
  reason := [convert(procname,string),"h is not indexed by TT",h,TT];
  return false;
 fi;

 for a in A do if h[{a}] <> 0 then
  reason := [convert(procname,string),"h({a}) <> 0",a,h[{a}]];
  return false;
 fi; od;

 for V in TT do
  u := h[V];
  if not (`is_element/RR`(u) and u >= 0 and u <= 1) then
   reason := [convert(procname,string),"h(V) is not in the unit interval",V,u];
   return false;
  fi;

  is_minimal := true;
  for U in TT do
   if U <> V and U minus V = {} then
    is_minimal := false;
    if h[U] > h[V] then return false; fi;
   fi;
  od;
  if is_minimal and h[V] <> 0 then
   reason := [convert(procname,string),"V is minimal in TT but h(V) <> 0",V,TT,h[V]];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_equal/tree_height_functions` := (A::set) -> (TT) -> proc(h1,h2) 
 local T;
 global reason;

 for T in TT do 
  if h1[T] <> h2[T] then
   reason := [convert(procname,string),"h1[T] <>  h2[T]",T,h1[T],h2[T]];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/tree_height_functions` := NULL;

######################################################################

`random_element/tree_height_functions` := (A::set) -> (TT) -> proc(d::posint := 12)
 local e,TS,T,h,parent,children;

 TS := sort([op(TT)],(U,V) -> nops(U) > nops(V));
 h := table();

 parent := parent_map(A)(TT);
 children := children_map(A)(TT);

 for T in TS do
  if children[T] = {} then
   h[T] := 0;
  elif parent[T] = FAIL then
   h[T] := rand(0..d)()/d;
  else
   e := h[parent[T]] * d;
   h[T] := rand(0..e)()/d;
  fi;
 od;

 return eval(h); 
end;

######################################################################

`list_elements/tree_height_functions` := NULL;
`count_elements/tree_height_functions` := NULL;

######################################################################

`is_singular/tree_height_functions` := (A::set) -> (TT) -> proc(h)
 local TS,n,i,j;

 TS := sort([op(TT)],(U,V) -> nops(U) < nops(V));
 n := nops(TS);
 for i from 1 to n do 
  if h[TS[i]] = 1 then return true; fi;
  for j from i+1 to n do
   if TS[i] minus TS[j] = {} and h[TS[i]] = h[TS[j]] then
    return true;
   fi;
  od;
 od;

 return false;
end;

######################################################################

`extend/tree_height_functions` := (A::set) -> (TT) -> proc(h)
 local he,TS,P,T,U;

 he := table;
 TS := sort([op(TT)],(U,V) -> nops(U) < nops(V));

 P := `list_elements/nonempty_subsets`(A);
 for T in P do 
  he[T] := 1;
  for U in TS do
   if T minus U = {} then
    he[T] := h[U];
    break;
   fi;
  od;
 od;

 return eval(he);
end;

