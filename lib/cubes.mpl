######################################################################

`is_element/cubes` := (k::posint) -> (A::set) -> proc(f)
 local n,i,j;
 global reason;

 if not type(f,table) then
  reason := [convert(procname,string),"f is not a table",f];
  return false;
 fi;

 if map(op,{indices(f)}) <> A then
  reason := [convert(procname,string),"f is not indexed by A",f,A];
  return false;
 fi;
 
 n := nops(A);
 for i from 1 to n do
  if not `is_element/single_cubes`(k)(f[A[i]]) then
   reason := [convert(procname,string),"f(a) is not a single cube",A[i],f(A[i]),reason];
   return false;
  fi;

  for j from 1 to i-1 do
   if `overlap/single_cubes`(k)(f[A[j]],f[A[i]]) then
    reason := [convert(procname,string),"subcubes f(a) and f(b) overlap",A[i],A[j],f(A[i]),f(A[j])];
    return false;
   fi;
  od;
 od;

 return true;
end;

`is_equal/cubes` := (k::posint) -> (A::set) -> proc(f,g)
 local a;
 global reason;

 for a in A do 
  if not `is_equal/single_cubes`(k)(f[a],g[a]) then
   reason := [convert(procname,string),"f[a] <> g[a]",a,f[a],g[a]];
   return false;
  fi;
 od;

 return true;
end;

`is_leq/cubes` := NULL;

`random_element/cubes` := (N::posint) -> (A::set) -> proc()
 local d,f,a;

 d := 5;

 while true do
  d := d+1;
  f := table();
  for a in A do 
   f[a] := `random_element/single_cubes`(N)(d);
  od;

  if `is_element/cubes`(N)(A)(f) then
   return(eval(f));
  fi;

  if d > 1000 then return FAIL; fi;
 od;
end;

`list_elements/cubes` := NULL;
`count_elements/cubes` := NULL;

`draw/cubes` := (A::set) -> proc(f)
 local P,a;

 P := rectangle([0,0],[1,1],colour=blue,style=line);
 for a in A do
  P := P,rectangle(f[a][1],f[a][2],colour=red);
 od;
 display(P,scaling=constrained,axes=none);
end;

`centres/cubes` := (k::posint) -> (A::set) -> proc(f)
 local g,a;

 g := table();
 for a in A do 
  g[a] := `centre/single_cubes`(k)(f[a]);
 od;

 return eval(g);
end;

