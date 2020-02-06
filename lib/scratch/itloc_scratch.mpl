######################################################################

`is_element/P/itloc` := (N::set(nonnegint)) -> (AA) -> (T) -> proc(TT)
 `is_element/M1/itloc`(N)(AA)(TT) and `omega/itloc`(TT) = T;
end:

`is_leq/P/itloc` := (N::set(nonnegint)) -> (AA) -> (T) -> proc(TT0,TT1)
 `and`(seq(TT0[i] minus TT1[i] = {},i=1..nops(TT0)));
end:

`list_elements/P/itloc` := (N::set(nonnegint)) -> (AA) -> proc(T)
 local BB,L;
 
 BB := `cap/itloc`(AA,T);
 L := `list_elements/M1/itloc`(T)(BB);
 L := select(TT -> `omega/itloc`(TT) = T,L);
 return L;
end:

######################################################################

`is_element/P_star/itloc` := (N) -> (AA) -> (T) -> (iu) -> proc(TT)
 local i,u;
 
 i,u := op(iu);

 if not(`is_element/P/itloc`(N)(AA)(T)(TT)) then
  return false;
 fi;

 if max(u,op(TT[i])) <> u then
  return false;
 fi;

 return true;
end:

`Alpha/itloc` := (N) -> (AA) -> (T) -> (iu) -> proc(TT)
 local i,u,r,UU;
 
 i,u := op(iu);

 if max(op(TT[i])) < u then
  return TT;
 fi;

 r := nops(AA);
 UU := [
  seq(TT[k],k=1..i),
  TT[i+1] union {u},
  seq(TT[k],k=i+2..r)
 ];

 return UU;
end:

`Beta/itloc` := (N) -> (AA) -> (T) -> (iu) -> proc(TT)
 local i,u,r,UU;
 
 i,u := op(iu);

 if max(op(TT[i])) < u then
  return TT;
 fi;

 r := nops(AA);
 UU := [
  seq(TT[k],k=1..i-1),
  TT[i] minus {u},
  TT[i+1] union {u},
  seq(TT[k],k=i+2..r)
 ];

 return UU;
end:

######################################################################

`is_element/MM/itloc` := (N) -> (AA) -> (T) -> (i) -> proc(TT)
 local a,r,k,UU;
 
 if not(`is_element/P/itloc`(N)(AA)(T)(TT)) then
  return false;
 fi;

 a := `bot/threads/itloc`(`cap/itloc`(AA,T));
 r := nops(AA);
 UU := [
  select(t -> t <= a[1],T),
  seq(select(t -> a[k-1] <= t and t <= a[k],T),k=2..r)
 ];

 for k from 1 to i do
  if TT[k] <> UU[k] then return false; fi;
 od;

 return true;
end:

`is_element/NN/itloc` := (N) -> (AA) -> (T) -> (i) -> proc(TT)
 local a,r,k,UU;
 
 if not(`is_element/P/itloc`(N)(AA)(T)(TT)) then
  return false;
 fi;

 a := `bot/threads/itloc`(`cap/itloc`(AA,T));
 r := nops(AA);
 UU := [
  select(t -> t <= a[1],T),
  seq(select(t -> a[k-1] <= t and t <= a[k],T),k=2..r)
 ];

 for k from 1 to i do
  if TT[k] <> UU[k] then return false; fi;
 od;

 if i = 0 and not(member(min(op(T)),TT[1])) then
  return false;
 fi;
 
 if i > 0 and not(member(a[i],TT[i+1])) then
  return false;
 fi;
 
 return true;
end:

`is_element/LL/itloc` := (N) -> (AA) -> (T) -> (iu) -> proc(TT)
 local i,u,a,r,k,UU;

 i,u := op(iu);
 
 if not(`is_element/NN/itloc`(N)(AA)(T)(i-1)(TT)) then
  return false;
 fi;

 if max(op(TT[i])) > u then
  return false;
 fi;

 return true;
end:

`theta/itloc` := (N) -> (AA) -> (T) -> (i) -> proc(TT)
 local a,r;
 
 a := `bot/threads/itloc`(`cap/itloc`(AA,T));
 r := nops(AA);
 
 return [
  seq(TT[k],k=1..i),
  TT[i+1] union {a[i]},
  seq(TT[k],k=i+2..r)
 ];
end;