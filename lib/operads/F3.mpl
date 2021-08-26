`delta/F3` := (N::posint) -> (x) -> [
 `delta/F`(N)({1,2,3})(1,2)(x),
 `delta/F`(N)({1,2,3})(2,3)(x),
 `delta/F`(N)({1,2,3})(3,1)(x)
];

`Delta/F3` := (N::posint) -> (u) -> [u,u];

`f_plus/F3` := (N::posint) -> proc(vw)
 local v,w;
 v,w := op(vw);
 return [-~ v,v,v -~ w];
end:

`f_minus/F3` := (N::posint) -> proc(vw)
 local v,w;
 v,w := op(vw);
 return [-~ v,v,w -~ v];
end:

`g_plus/F3`  := (N::posint) -> proc(vw)
 local v,w;
 v,w := op(vw);
 return [v,-~ w, -~ v];
end:

`g_minus/F3`  := (N::posint) -> proc(vw)
 local v,w;
 v,w := op(vw);
 return [v,-~ v, -~ w];
end:

######################################################################

`is_element/X/F3` := (N::posint) -> proc(xyz)
 global reason;
 local tag,x,y,z;

 tag := "is_element/X/F3";

 if not(type(xyz,list) and nops(xyz) = 3) then
  reason := [tag,"xyz is not a list of length 3",xyz];
  return false;
 fi;

 x,y,z := op(xyz);
 if not(`is_element/R`(N)(x) and 
        `is_element/R`(N)(y) and 
        `is_element/R`(N)(z)) then
  reason := [tag,"x, y and z are not vectors in R^N",x,y,z];
  return false;
 fi;

 if (x -~ y = [0$N] or y -~ z = [0$N] or z -~ x = [0$N]) then
  reason := [tag,"x, y and z are not distinct",x,y,z];
  return false;
 fi;

 if x +~ y <> [0$N] then
  reason := [tag,"x+y <> 0",x,y];
  return false;
 fi;

 if `norm_2/R`(N)(x) <> 1 or `norm_2/R`(N)(y) <> 1 then
  reason := [tag,"x and y are not normalised",x,y];
  return false;
 fi;

 return true;
end:

`is_equal/X/F3` := (N::posint) -> (xyz0,xyz1) ->
  evalb(simplify(xyz0 -~ xyz1) = [[0$N]$3]);

`is_leq/X/F3` := NULL;
`list_elements/X/F3` := NULL;
`count_elements/X/F3` := NULL;

`random_element/X/F3` := (N::posint) -> proc()
 local x,y,z;
 x := `random_element/sphere`(N-1)();
 y := -~ x;
 z := `random_element/R`(N)();
 while z = x or z = y do 
  z := `random_element/R`(N)();
 od;
 return [x,y,z];
end:

######################################################################

`is_element/Y/F3` := (N::posint) -> proc(xyz)
 local tag,x,y,z;
 global reason;
 
 tag := "is_element/Y/F3";

 if not(`is_element/X/F3`(N)(xyz)) then
  reason := [tag,"xyz in not in X",xyz,reason];
  return false;  
 fi;

 x,y,z := op(xyz);
 if `d_2/R`(N)(z,x) <> 1 and `d_2/R`(N)(z,y) <> 1 then
  reason := [tag,"z is not at distance 1 from x or y",x,y,z];
  return false;  
 fi; 

 return true;
end:

`is_equal/Y/F3` := (N::posint) -> (xyz0,xyz1) ->
  evalb(simplify(xyz0 -~ xyz1) = [[0$N]$3]);

`is_leq/Y/F3` := NULL;
`list_elements/Y/F3` := NULL;
`count_elements/Y/F3` := NULL;

`random_element/Y/F3` := (N::posint) -> proc()
 local x,y,w,z;
 x := `random_element/sphere`(N-1)();
 y := -~ x;
 w := `random_element/sphere`(N-1)();
 if rand(0..1)() = 0 then
  z := x +~ w;
 else 
  z := y +~ w;
 fi;
 return [x,y,z];
end:

######################################################################

`is_element/D_plus/F3` := (N::posint) -> proc(xyz)
 local tag,x,y,z;
 global reason;
 tag := "is_element/D_plus/F3";

 if not(`is_element/X/F3`(N)(xyz)) then
  reason := [tag,"xyz in not in X",xyz,reason];
  return false;  
 fi;

 x,y,z := op(xyz);
 if `d_2/R`(N)(z,y) > 1 then
  reason := [tag,"z is not at distance <= 1 from y",x,y,z];
  return false;  
 fi; 

 return true;
end:

`is_equal/D_plus/F3` := (N::posint) -> (xyz0,xyz1) ->
  evalb(simplify(xyz0 -~ xyz1) = [[0$N]$3]);

`is_leq/D_plus/F3` := NULL;
`list_elements/D_plus/F3` := NULL;
`count_elements/D_plus/F3` := NULL;

`random_element/D_plus/F3` := (N::posint) -> proc()
 local x,y,w,z;
 x := `random_element/sphere`(N-1)();
 y := -~ x;

 if rand(0..5)() = 0 then
  z := [0$N];
 else 
  w := `random_element/sphere`(N-1)() *~ rand(1..5)()/5;
  z := y +~ w;
 fi;
 return [x,y,z];
end:

######################################################################

`is_element/D_minus/F3` := (N::posint) -> proc(xyz)
 local tag,x,y,z;
 global reason;

 tag := "is_element/D_minus/F3";

 if not(`is_element/X/F3`(N)(xyz)) then
  reason := [tag,"xyz in not in X",xyz,reason];
  return false;  
 fi;

 x,y,z := op(xyz);
 if `d_2/R`(N)(z,x) > 1 then
  reason := [tag,"z is not at distance <= 1 from x",x,y,z];
  return false;  
 fi; 

 return true;
end:

`is_equal/D_minus/F3` := (N::posint) -> (xyz0,xyz1) ->
  evalb(simplify(xyz0 -~ xyz1) = [[0$N]$3]);

`is_leq/D_minus/F3` := NULL;
`list_elements/D_minus/F3` := NULL;
`count_elements/D_minus/F3` := NULL;

`random_element/D_minus/F3` := (N::posint) -> proc()
 local x,y,w,z;
 x := `random_element/sphere`(N-1)();
 y := -~ x;

 if rand(0..5)() = 0 then
  z := [0$N];
 else 
  w := `random_element/sphere`(N-1)() *~ rand(1..5)()/5;
  z := x +~ w;
 fi;
 return [x,y,z];
end:

######################################################################

`is_element/D_zero/F3` := (N::posint) -> proc(xyz)
 local tag,x,y,z;
 global reason;
 
 tag := "is_element/D_zero/F3";

 if not(`is_element/X/F3`(N)(xyz)) then
  reason := [tag,"xyz in not in X",xyz,reason];
  return false;  
 fi;

 x,y,z := op(xyz);
 if `d_2/R`(N)(z,x)^2 < 1 or `d_2/R`(N)(z,y)^2 < 1 then
  reason := [tag,"z is not at distance >= 1 from x and y",x,y,z];
  return false;  
 fi; 

 return true;
end:

`is_equal/D_zero/F3` := (N::posint) -> (xyz0,xyz1) ->
  evalb(simplify(xyz0 -~ xyz1) = [[0$N]$3]);

`is_leq/D_zero/F3` := NULL;
`list_elements/D_zero/F3` := NULL;
`count_elements/D_zero/F3` := NULL;

`random_element/D_zero/F3` := (N::posint) -> proc()
 local x,y,w,z,r,i;
 x := `random_element/sphere`(N-1)();
 y := -~ x;

 z := x;
 r := 0;
 while r < 1 do
  if rand(0..5)() = 0 then
   w := `random_element/sphere`(N-1)();
   if rand(0..1)() = 0 then
    z := x +~ w;
   else
    z := y +~ w;
   fi;
  else
   z := `random_element/sphere`(N-1)(100) *~ (rand(1..300)()/100);
  fi;
  r := min(add((x[i]-z[i])^2,i=1..N),add((y[i]-z[i])^2,i=1..N));
 od:

 return [x,y,z];
end:

######################################################################

`q_plus/F3` := (N::posint) -> proc(xyz)
 local x,y,z;
 x,y,z := op(xyz);
 return y +~ (z -~ y) /~ `norm_2/R`(N)(z -~ y); 
end:

######################################################################

`q_minus/F3` := (N::posint) -> proc(xyz)
 local x,y,z;
 x,y,z := op(xyz);
 return y +~ (z -~ x) /~ `norm_2/R`(N)(z -~ x); 
end:

######################################################################

`q_zero/F3` := (N::posint) -> proc(xyz)
 local x,y,z;
 x,y,z := op(xyz);
 if z = [0$N] then
  return [0$N];
 else
  return (2*`dot/R`(N)(y,z)/`norm_2/R`(N)(z)^2) *~ z;
 fi;
end:

######################################################################

`q/F3` := (N::posint) -> proc(xyz)
 local x,y,z;
 x,y,z := op(xyz);
 if   `is_element/D_plus/F3`(N)(xyz) then
  return `q_plus/F3`(N)(xyz);
 elif `is_element/D_minus/F3`(N)(xyz) then
  return `q_minus/F3`(N)(xyz);
 else
  return `q_zero/F3`(N)(xyz);
 fi;
end:

`r/F3` := (N::posint) -> proc(xyz)
 local x,y,z,x0,y0,z0,n0;
 x,y,z := op(xyz);

 x0 := (x -~ y)/~2;
 n0 := `norm_2/R`(N)(x0);
 x0 := x0 /~ n0;
 y0 := -~ x0;
 z0 := (z -~ ((x +~ y)/~2))/~ n0;
 return [x0,y0,`q/F3`(N)([x0,y0,z0])];
end:

