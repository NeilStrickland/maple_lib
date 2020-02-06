######################################################################
# single_cubes(k) is the usual set of injective maps [0,1]^k -> [0,1]^k

`is_element/single_cubes` := (k::posint) -> proc(xy)
 local i,x,y;
 global reason;

 if not(type(xy,[[realcons$k],[realcons$k]])) then
  reason := [convert(procname,string),"xy is not in R^k x R^k",xy];
  return false;
 fi;

 x,y := op(xy);
 for i from 1 to k do
  if not(0 <= x[i] and x[i] < y[i] and y[i] <= 1) then
   reason := [convert(procname,string),"not (0 <= x[i] < y[i] <= 1)",i,x[i],y[i]];
   return false;
  fi;
 od;

 return true;
end;

`is_equal/single_cubes` := (k::posint) -> proc(xy1,xy2)
 global reason;

 if xy1 <> xy2 then
  reason := [convert(procname,string),"xy1 <> xy2",xy1,xy2];
  return false;
 fi;

 return true;
end:

`is_leq/single_cubes` := NULL;

`random_element/single_cubes` := (k::posint) -> proc(d := 6) 
 local r,x,y,i,s,t;

 r := rand(0..d);
 x := NULL;
 y := NULL;
 for i from 1 to k do
  s := 0;
  t := 0;
  while s = t do s := r(); t := r(); od;
  x := x,min(s,t)/d;
  y := y,max(s,t)/d;
 od;
 return [[x],[y]];
end;

`list_elements/single_cubes` := NULL;
`count_elements/single_cubes` := NULL;

`act/single_cubes` := (k::posint) -> (xy) -> (t) ->
 xy[1] +~ (t *~ (xy[2] -~ xy[1]));

`id/single_cubes` := (k::posint) -> [[0$k],[1$k]];

`compose/single_cubes` := (k::posint) -> (xy,uv) -> 
  map(`act/single_cubes`(k)(xy),uv);

`overlap/single_cubes` := (k::posint) -> proc(xy,uv)
 local x,y,u,v,i;

 x,y := op(xy);
 u,v := op(uv);
 for i from 1 to k do
  if max(x[i],u[i]) >= min(y[i],v[i]) then
   return false;
  fi;
 od;
 return true;
end;

`centre/single_cubes` := (k::posint) -> proc(xy)
 (xy[1] +~ xy[2]) /~ 2;
end;

