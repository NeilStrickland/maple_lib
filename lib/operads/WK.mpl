######################################################################

`is_element/WK` := (A::set) -> proc(TTxl)
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
  if not(`is_element/stasheff_star`(children[T])(x[T])) then
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

######################################################################

`is_interior/WK` := (A::set) -> proc(TTxl)
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

######################################################################

`is_reduced/WK` := (A::set) -> proc(TTxl)
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

######################################################################

`reduce_once/WK` := (A::set) -> proc(TTxl,T)
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
 for X in C minus {T} do y[X] := `eta/stasheff_star`({X}); od;
 y[T] := x[T];

 z := `gamma/stasheff_star`(B,C)(p)(x[U],y);

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

`reduce/WK` := (A::set) -> proc(TTxl)
 local is_reduced,X,TT,x,l,T;

 is_reduced := false;
 X := TTxl;

 while not(is_reduced) do
  TT,x,l := op(X);
  is_reduced := true;

  for T in TT do
   if l[T] = 0 then 
    is_reduced := false;
    X := `reduce_once/WK`(A)(X,T);
    break;
   fi;
  od:
 od;

 return X;
end;

######################################################################

`is_equal/WK` := (A::set) -> proc(X0,X1)
 local Y0,Y1,TT0,TT1,x0,x1,l0,l1,children,T;
 global reason;

 Y0 := `reduce/WK`(A)(X0);
 Y1 := `reduce/WK`(A)(X1);
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
   if not(`is_equal/stasheff_star`(children[T])(x0[T],x1[T])) then
    reason := [convert(procname,string),"x0[T] <> x1[T]",T,x0[T],x1[T],reason];
    return false;
   fi;
  fi;
 od;

 return true;
end;

######################################################################

`is_leq/WK` := NULL;

######################################################################

`random_element/WK` := (A::set) -> proc()
 local TT,x,l,TT1,T,n,children,d;

 d := 3;
 TT := `random_element/full_trees`(A)();

 TT1 := select(U -> nops(U) > 1,TT);

 x := table();
 l := table();

 children := `children_map`(A)(TT);
 for T in TT1 do
  x[T] := `random_element/stasheff_star`(children[T])();
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

`list_elements/WK` := NULL;
`count_elements/WK` := NULL;

######################################################################

`eta/WK` := proc(A::set) 
 if nops(A) <> 1 then return FAIL; fi;
 return [[op(A)],table([])];
end;

`gamma/WK` := (A::set,B::set) -> (p) -> proc(M,N)
 local F,TT,SS,UU,x,y,z,l,m,n,pi,T,T1,C,C1,U,b,L,children;

 F := fibres(A,B)(p);

 TT,x,l := op(M);
 children := children_map(B)(TT);
 pi := table();
 for T in TT do
  pi[T] := map(op,map(b -> F[b],T));
 od;
 
 SS := table();
 y := table();
 m := table();

 for b in B do 
  SS[b],y[b],m[b] := op(N[b]);
 od;

 UU := {seq(op(SS[b]),b in B)};
 z := table();
 n := table();

 for T in TT do
  T1 := pi[T];
  if nops(T1) > 0 then
   UU := {op(UU),T1};
   n[T1] := l[T];
   if nops(T) = 1 then
    if nops(T1) > 1 then
     z[T1] := eval(y[op(T)][T1]);
    fi;
   else
    C := children[T];
    C1 := map(U -> pi[U],C);
    z[T1] :=  `act/stasheff_star`(C,C1)(pi)(x[T]);
   fi;
  fi;
 od;

 for b in B do 
  for U in SS[b] do
   n[U] := m[b][U];
   if nops(U) > 1 then  
    z[U] := y[b][U];
   fi;
  od;
 od;

 L := [UU,eval(z),eval(n)];
 L := `reduce/WK`(A)(L);
 return L;
end;

######################################################################

`phi/WK/K` := (A::set) -> proc(TTxl)
 local SS,TT,x,l,TT1,s,t,u,RR,R,T,f,parent,children,J,J1,JJ,i,j,k,n,m;

 TT,x,l := op(TTxl);

 TT1 := select(U -> nops(U) > 1,TT);
 parent := `parent_map`(A)(TT);
 children := `children_map`(A)(TT);

 s := table():
 RR := table():

 for T in TT1 do
  RR[T],s[T] := op(x[T]);
 od:

 R := `phi/WK/K/aux`(A,RR);
 u := table():
 n := nops(A);
 JJ := {seq(seq({seq(R[k],k=i..j)},j=i..n),i=1..n)};

 for J in JJ do
  if member(J,TT) then
   u[J] := (1+l[J])/2;
  else
   SS := select(T -> (J minus T = {}),TT);
   m := min(op(map(nops,SS)));
   T := select(T -> (nops(T) = m),SS)[1];
   J1 := select(U -> (U intersect J <> {}),children[T]);
   if {op(map(op,J1))} = J then
    u[J] := s[T][J1]/2;
   else
    u[J] := 0;
   fi;   
  fi;
 od;

 return [R,eval(u)];
end;

########################################

`phi/WK/K/aux` := proc(T,UU)
  if nops(T) = 1 then
   return [op(T)];
  else
   map(op,map(U -> `phi/WK/K/aux`(U,UU),UU[T]));
  fi;
 end;

######################################################################

`theta/K/WK` := (A::set) -> proc(Rt)
 local R,t,r,T,TT,RR,s,l,x,C,m,J,J1,i,j,k,children;

 R,t := op(Rt);

 r := table();
 for i from 1 to nops(R) do
  r[R[i]] := i;
 od;
 
 TT := select(J -> t[J] > 1/2,map(op,{indices(t)}));
 RR := table():
 s := table():
 l := table():
 x := table():

 children := `children_map`(A)(TT);
 for T in TT do
  l[T] := 2*t[T] - 1;
  C := [op(children[T])];
  C := sort(C,(U0,U1) -> (r[U0[1]] < r[U1[1]]));
  RR[T] := C;
  m := nops(C);
  if m > 1 then
   s[T] := table():
   for i from 1 to m do 
    for j from i to m do 
     J1 := {seq(C[k],k=i..j)};
     J := map(op,J1);
     s[T][J1] := min(1,2*t[J]);
    od;
   od;
   x[T] := [RR[T],eval(s[T])];
  fi;
 od: 

 return [TT,eval(x),eval(l)];
end:
