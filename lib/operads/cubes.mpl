######################################################################

`eta/cubes` := (k::posint) -> (A::set) -> 
 `if`(nops(A) = 1,table(op(A) = `id/single_cubes`(k)),FAIL);

`gamma/cubes` := (k::posint) -> (A::set,B::set) -> (p) -> proc(f,g)
 local a,h;

 h := table();
 for a in A do 
  h[a] := `compose/single_cubes`(k)(f[p[a]],g[p[a]][a]);
 od;
 return eval(h);
end;

