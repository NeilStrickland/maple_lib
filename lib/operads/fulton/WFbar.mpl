######################################################################

`is_element/WFbar` := (N::posint) -> (A::set) -> proc(TTxl)
 local TT,x,l,TT1,T,n,u,children;
 global reason;

 if not(type(TTxl,list) and nops(TTxl) = 3) then
  reason := [convert(procname,string),"TTxl cannot be split as [TT,x,l]",TTxl];
  return false;
 fi;

 TT,x,l := op(TTxl);

 if not(`is_element/trees`(A)(TT)) then
  reason := [convert(procname,string),"TT is not a tree on A",TT,A];
  return false;
 fi;

 TT1 := select(U -> nops(U) > 1,TT);

 if not(type(x,table)) then
  reason := [convert(procname,string),"x is not a table",x];
  return false;
 fi;

 if map(op,{indices(x)}) <> TT1 then
  reason := [convert(procname,string),"x is not indexed by TT1",x,TT1];
  return false;
 fi;

 children := `children_map`(A)(TT);
 for T in TT1 do
  if not(`is_element/Fbar`(N)(children[T])(x[T])) then
   reason := [convert(procname,string),"x[T] has invalid type",T,x[T],reason];
   return false;
  fi;
 od;

 if not(type(l,table)) then
  reason := [convert(procname,string),"l is not a table",l];
  return false;
 fi;

 if map(op,{indices(l)}) <> TT then
  reason := [convert(procname,string),"l is not indexed by TT",l,TT];
  return false;
 fi;

 n := nops(A);

 for T in TT do
  if not(`is_element/RR`(l[T]) and l[T] >= 0 and l[T] <= 1) then
   reason := [convert(procname,string),"l[T] is not in the unit interval",T,l[T]];
   return false;
  fi;

  if nops(T) = 1 and l[T] <> 1 then
   reason := [convert(procname,string),"l[{a}] <> 1",op(T),l[T]];
   return false;
  fi;

  if nops(T) = n and l[T] <> 1 then
   reason := [convert(procname,string),"l[A] <> 1",T,l[T]];
   return false;
  fi;
 od;

 return true;
end;

`is_interior/WFbar` := (N::posint) -> (A::set) -> proc(TTxl)
 local TT,x,l,n,T;
 global reason;

 TT,x,l := op(TTxl);
 n := nops(A);

 for T in TT do
  if nops(T) > 1 and nops(T) < n and l[T] = 1 then
   reason := [convert(procname,string),"not interior, l[T] = 1",T];
   return false;
  fi;
 od:

 return true;
end;

`is_reduced/WFbar` := (N::posint) -> (A::set) -> proc(TTxl)
 local TT,x,l,T;
 global reason;

 TT,x,l := op(TTxl);

 for T in TT do
  if l[T] = 0 then
   reason := [convert(procname,string),"not reduced, l[T] = 0",T];
   return false;
  fi;
 od:

 return true;
end;

`reduce_once/WFbar` := (N::posint) -> (A::set) -> proc(TTxl,T)
 local TT,x,l,parent,children,n,TT1,x1,l1,U,B,C,X,p,y,z;

 TT,x,l := op(TTxl);

 parent := `parent_map`(A)(TT);
 children := `children_map`(A)(TT);

 TT1 := TT minus {T};

 U := parent[T];
 C := children[U];
 B := C minus {T} union children[T];

 p := table();
 for X in C minus {T} do p[X] := X; od;
 for X in children[T] do p[X] := T; od;

 y := table();
 for X in C minus {T} do y[X] := `eta/Fbar`(N)({X}); od;
 y[T] := x[T];

 z := `gamma/Fbar`(N)(B,C)(p)(x[U],y);

 x1 := table();
 l1 := table();

 for X in TT1 do
  l1[X] := l[X];
  if nops(X) > 1 then
   x1[X] := `if`(X = U,eval(z),eval(x[X]));
  fi;
 od;

 return([TT1,eval(x1),eval(l1)]);
end;

`reduce/WFbar` := (N::posint) -> (A::set) -> proc(TTxl)
 local is_reduced,X,TT,x,l,T;

 is_reduced := false;
 X := TTxl;

 while not(is_reduced) do
  TT,x,l := op(X);
  is_reduced := true;

  for T in TT do
   if l[T] = 0 then 
    is_reduced := false;
    X := `reduce_once/WFbar`(N)(A)(X,T);
    break;
   fi;
  od:
 od;

 return X;
end;

`is_equal/WFbar` := (N::posint) -> (A::set) -> proc(X0,X1)
 local Y0,Y1,TT0,TT1,x0,x1,l0,l1,children,T;
 global reason;

 Y0 := `reduce/WFbar`(N)(A)(X0);
 Y1 := `reduce/WFbar`(N)(A)(X1);
 TT0,x0,l0 := op(Y0);
 TT1,x1,l1 := op(Y1);

 if TT0 <> TT1 then
  reason := [convert(procname,string),"TT0 <> TT1",TT0,TT1];
  return false;
 fi;

 children := `children_map`(A)(TT0);

 for T in TT0 do
  if l0[T] <> l1[T] then
   reason := [convert(procname,string),"l0[T] <> l1[T]",T,l0[T],l1[T]];
   return false;
  fi;

  if nops(T) > 1 then
   if not(`is_equal/Fbar`(N)(children[T])(x0[T],x1[T])) then
    reason := [convert(procname,string),"x0[T] <> x1[T]",T,x0[T],x1[T],reason];
    return false;
   fi;
  fi;
 od;

 return true;
end;

`is_leq/WFbar` := NULL;

`random_element/WFbar` := (N::posint) -> (A::set) -> proc()
 local TT,x,l,TT1,T,n,children,d;

 d := 3;
 TT := `random_element/full_trees`(A)();

 TT1 := select(U -> nops(U) > 1,TT);

 x := table();
 l := table();

 children := `children_map`(A)(TT);
 for T in TT1 do
  x[T] := `random_element/Fbar`(N)(children[T])();
 od;

 n := nops(A);

 for T in TT do
  if nops(T) = 1 or nops(T) = n then 
   l[T] := 1;
  else 
   l[T] := rand(0..d)()/d;
  fi;
 od;

 return [TT,eval(x),eval(l)];
end;

`list_elements/WFbar` := NULL;
`count_elements/WFbar` := NULL;
