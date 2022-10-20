bar := proc()
 local n,m,i,j,u,a,v,ac,av,x,y;
 n := nargs;
 for i from 1 to n do
  u := seq(args[j],j=1..i-1);
  a := args[i];
  v := seq(args[j],j=i+1..n);
  if a = 0 then
   return 0;
  elif type(a,`+`) then
   return map(t -> bar(u,t,v),a);
  elif type(a,`*`) then
   ac,av := selectremove(type,a,rational);
   if ac <> 1 then
    return ac * bar(u,av,v);
   fi;
  elif type(a,specfunc(bar)) then
   return bar(u,op(a),v);
  elif type(a,specfunc(bracket)) then
   m := nops(a);
   if m = 0 then
    return FAIL;
   elif m = 1 then
    return bar(u,op(a),v);
   else
    x := op(1,a);
    y := bracket(op(2..-1,a));
    return bar(u,x,y,v) - bar(u,y,x,v);
   fi; 
  fi;
 od;
 return 'procname'(args);
end:

`mult/free_algebra` := () -> bar(args);

`commutator/free_algebra` := () -> bar(bracket(args));

`basis/free_algebra` := (A::set) -> proc(d::nonnegint)
 local i,B,a,b;
 B := [bar()];
 for i from 1 to d do 
  B := [seq(seq(bar(op(b),a),a in A),b in B)];
 od:
 return B;
end:

`vec/free_algebra` := (A::set) -> (d::nonnegint) -> proc(u)
 local n,ub,uc,T,B,i;
 global `vec_table/free_algebra`;
 n := nops(A);
 if u = 0 then
  return [0$(n^d)];
 elif type(u,`+`) then
  return map(`vec/free_algebra`(A)(d),u); 
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
  if not(type(`vec_table/free_algebra`[A,d],table)) then
   T := table():
   B := `basis/free_algebra`(A)(d);
   for i from 1 to n^d do
    T[B[i]] := [0$(i-1),1,0$(n!-i)];
   od:
   `vec_table/free_algebra`[A,d] := eval(T);
  fi;
  return uc *~ `vec_table/free_algebra`[A,d][ub];
 fi;
end:

