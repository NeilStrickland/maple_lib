`basis/ass_operad` := (A::set) -> map(u -> bar(op(u)),`list_elements/ord`(A));

`vec/ass_operad` := (A::set) -> proc(u)
 local n,ub,uc,T,B,i;
 global `vec_table/ass_operad`;
 n := nops(A);
 if u = 0 then
  return [0$(n!)];
 elif type(u,`+`) then
  return map(`vec/ass_operad`(A),u); 
 else
  if type(u,specfunc(bar)) then
   ub := u;
   uc := 1;
  elif type(u,`*`) then
   ub,uc := selectremove(type,u,specfunc(bar));
   ub := map(op,bar(ub));
  else
   return FAIL;
  fi;
  if not(type(`vec_table/ass_operad`[A],table)) then
   T := table():
   B := `basis/ass_operad`(A);
   for i from 1 to n! do
    T[B[i]] := [0$(i-1),1,0$(n!-i)];
   od:
   `vec_table/ass_operad`[A] := eval(T);
  fi;
  return uc *~ `vec_table/ass_operad`[A][ub];
 fi;
end:

