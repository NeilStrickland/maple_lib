# An RZ_set is a subset of the circle R/Z that can be expressed as
# a finite union of half-open intervals [u,v).  Any such set can
# be expressed uniquely as
# [t[1],t[2]) u [t[3],t[4]) u ... u [t[2*n-1],t[2*n]) with
# 0 <= t[0] < t[1] < ... < t[2*n] <= 1.

`is_element/RZ_set` := proc(T)
 local n,i;
 
 if not type(T,list(realcons)) then return false; fi;
 n := nops(T)/2;
 if not(type(n,nonnegint)) then return false; fi;
 if n = 0 then return true; fi;
 if T[1] < 0 or T[2*n] > 1 then return false; fi;
 for i from 1 to 2*n-1 do
  if T[i+1] <= T[i] then return false; fi;
 od;
 return true;
end:

`is_equal/RZ_set` := proc(T,U)
 if nops(T) <> nops(U) then return false; fi;
 return evalb(simplify({0,op(T -~ U)}) = {0});
end:

`is_leq/RZ_set` := proc(T,U)
 evalb(`intersect/RZ_set`(T,`complement/RZ_set`(U)) = `empty/RZ_set`);
end:

`list_elements/RZ_set` := NULL:
`count_elements/RZ_set` := NULL:

`random_element/RZ_set` := proc()
 local n,S,T,i;
 
 n := rand(0..5)();
 S := {};
 while nops(S) < 2*n do
  S := {seq(rand(0..719)(),i=1..2*n)};
 od:
 T := sort([op(S)] /~ 720);
 T := `shift/RZ_set`(`random_element/RZ`())(T);
 return T;
end:

`length/RZ_set` := proc(T) local i; add((-1)^i * T[i],i=1..nops(T)); end:

`bot/RZ_set`   := []:
`empty/RZ_set` := []:
`top/RZ_set`   := [0,1];
`RZ/RZ_set`    := [0,1];

`complement/RZ_set` := proc(T)
 local n,U;
 n := nops(T)/2;
 if n = 0 then return [0,1]; fi;
 U := NULL;
 if T[1] > 0 then U := U,0,T[1]; fi;
 U := U,op(2..2*n-1,T);
 if T[2*n] < 1 then U := U,T[2*n],1; fi;
 U := [U];
 return U;
end:

`add_interval/RZ_set` := proc(T,u,v)
 local n,i,j,k,a,b;
 if nops(T) = 0 then return [u,v]; fi;
 n := nops(T)/2;
 i := 0;
 while i < n and T[2*i+2] < u do i := i+1; od;
 if i = n then return [op(T),u,v]; fi;
 j := i+1;
 while j <= n and T[2*j-1] <= v do j := j+1; od;
 a := min(u,T[2*i+1]);
 b := max(v,`if`(j = 1,0,T[2*j-2]));
 return [seq(T[k],k=1..2*i),a,b,seq(T[k],k=2*j-1..2*n)];
end:

`union/RZ_set` := proc()
 local U,T,n,i,j;
 if nargs = 0 then
  return `bot/RZ_set`;
 else
  U := args[1];
  for i from 2 to nargs do
   T := args[i];
   n := nops(T)/2;
   for j from 1 to n do
    U := `add_interval/RZ_set`(U,T[2*j-1],T[2*j]);
   od;
  od:
  return U;
 fi;
end:

`intersect/RZ_set` := proc()
 local T,U,V,n,m,i,j,a,b;
 if nargs = 0 then
  return `top/RZ_set`;
 elif nargs = 1 then
  return args[1];
 elif nargs > 2 then
  return `intersect/RZ_set`(args[1],`intersect/RZ_set`(args[2..-1]));
 else
  T := args[1];
  U := args[2];
  n := nops(T)/2;
  m := nops(U)/2;
  V := NULL;
  for i from 1 to n do
   for j from 1 to m do
    a := max(T[2*i-1],U[2*j-1]);
    b := min(T[2*i],U[2*j]);
    if a < b then
     V := V,[a,b];
    fi;
   od;
  od;
  V := sort([V],(x,y) -> (x[1] < y[1]));
  V := map(op,V);
  return V;
 fi;
end:

`symdiff/RZ_set` := proc(T,U)
 local A,B;
 
 A := `intersect/RZ_set`(T,`complement/RZ_set`(U));
 B := `intersect/RZ_set`(U,`complement/RZ_set`(T));
 return(`union/RZ_set`(A,B));
end:

`dist/RZ_set` := proc(T,U) `length/RZ_set`(`symdiff/RZ_set`(T,U)); end:

`shift/RZ_set` := (t) -> proc(T)
 local U,n,i,j;
 if T = [] then return []; fi;
 
 U := T +~ t;
 U := U -~ floor(U[1]);
 n := nops(U)/2;
 if U[2*n] <= 1 then return U; fi;

 i := 0;
 while i < n and U[2*i+2] <= 1 do i := i+1; od;
 if U[2*i+1] < 1 then
  if U[2*n] - 1 = U[1] then
   return [0,seq(U[j]-1,j=2*i+2..2*n-1),seq(U[j],j=2..2*i+1),1];
  else
   return [0,seq(U[j]-1,j=2*i+2..2*n),seq(U[j],j=1..2*i+1),1];
  fi;
 else 
  if U[2*n]-1 = U[1] then
   return [seq(U[j]-1,j=2*i+1..2*n-1),seq(U[j],j=2..2*i)];
  else
   return [seq(U[j]-1,j=2*i+1..2*n),seq(U[j],j=1..2*i)];
  fi;
 fi;
end:

`interval/RZ_set` := proc(a,b)
 local a0,b0;

 a0 := a - floor(a);
 b0 := b - floor(b);
 if a0 < b0 then
  return [a0,b0];
 elif a0 = b0 then
  return [];
 else 
  return [0,b0,a0,1];
 fi;
end:

`unroll/RZ_set` := proc(T,k::posint := 2)
 local n,i,j,t;
 n := nops(T)/2;
 if n=0 then return []; fi;
 if k = 1 then return T; fi;

 if T[1] = 0 and T[2*n] = 1 then
  return [seq(T[i],i=1..2*n-1),
          seq(seq(T[i]+j,i=2..2*n-1),j=1..k-2),
          seq(T[i]+k-1,i=2..2*n)];
 else
  return [seq(seq(t+j,t in T),j=0..k-1)];
 fi;
end:

`starts/RZ_set` := proc(T)
 local n,i;
 n := nops(T)/2;

 if n = 0 then return {}; fi;

 if T[1] = 0 and T[2*n] = 1 then
  return {seq(T[2*i-1],i=2..n)};
 else
  return {seq(T[2*i-1],i=1..n)};
 fi;
end:

`boundary/RZ_set` := proc(T)
 local n,i;
 n := nops(T)/2;

 if n = 0 then return {}; fi;

 if T[1] = 0 and T[2*n] = 1 then
  return {seq(T[i],i=2..2*n-1)};
 else
  return {seq(T[i],i=1..2*n)};
 fi;
end:

`are_crossed/RZ_set` := proc(T,U)
 local A,B,n,i;
 if `intersect/RZ_set`(T,U) <> `empty/RZ_set` then
  return true;
 fi;

 if nops(T) = 0 or nops(U) = 0 then
  return false;
 fi;
 
 A := `shift/RZ_set`(-T[1])(T);
 B := `shift/RZ_set`(-T[1])(U);
 i := 1;
 n := nops(A)/2;
 while i < n and A[2*i+2] <= B[1] do 
  i := i+1;
 od;
 if i = n then
  return false;
 else 
  return evalb(B[nops(B)] > A[2*i+1]);
 fi;
end:

`centroid_C/RZ_set` := proc(T)
 local n,l,t,i;
 n := nops(T)/2;
 if n = 0 then error("T is empty"); fi;
 l := `length/RZ_set`(T);
 evalf(add(int(exp(2*Pi*I*t),t=T[2*i-1]..T[2*i]),i=1..n)/l);
end:

`centroid_R2/RZ_set` := proc(T)
 local z;
 z := `centroid_C/RZ_set`(T);
 return([Re(z),Im(z)]);
end:
 
`flat_plot/RZ_set` := proc(T,y)
 local i;
 
 if T = [] then
  return NULL;
 else
  return 
   display(seq(line([T[2*i-1],y],[T[2*i],y],args[3..-1]),i=1..nops(T)/2),
           scaling=constrained,axes=none);
 fi;
end:

`plot/RZ_set` := proc(T,r := 1,c := [0,0])
 local A,i,n,z,t;
 if nargs > 3 then 
  A := args[4..-1];
 else
  A := NULL;
 fi;
 if T = [] then
  return NULL;
 else
  n := nops(T)/2;
  z := [seq(c +~ r *~ [cos(2*Pi*T[2*i-1]),sin(2*Pi*T[2*i-1])],i=1..n)];
  if T[1] = 0 and T[2*n] = 1 then
   z := [op(2..-1,z)];
  fi;
  return 
   display(
    seq(plot([c[1]+r*cos(2*Pi*t),
	      c[2]+r*sin(2*Pi*t),
	      t = T[2*i-1]..T[2*i]],
	      A),
	i=1..nops(T)/2),
    seq(line(0.95 *~ z[i],z[i],A),i=1..nops(z)),
    scaling=constrained,axes=none);
 fi;
end:

