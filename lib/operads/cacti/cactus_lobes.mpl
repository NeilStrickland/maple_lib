# A cactus lobe is a map f : R/Z -> R/Z of degree one that has 
# constant speed on some finite collection of half-open intervals,
# and speed zero on the complement of those intervals.  We encode
# f as a pair [c,T], where c = f(0) is in R/Z (as defined by
# `is_element/RZ`) and T is the half-open interval where the 
# speed is nonzero (as defined by `is_element/RZ_set`).

`is_element/cactus_lobes` := proc(cT)
 global reason;
 local c,T;

 if not(type(cT,list) and nops(cT) = 2) then
  reason := ["is_element/cactus_lobes","cT is not a list of length 2",cT];
  return false;  
 fi;

 c,T := op(cT);

 if not `is_element/RZ`(c) then
  reason := ["is_element/cactus_lobes","c is not in R/Z",c,cT];
  return false;  
 fi;

 if not `is_element/RZ_set`(T) then
  reason := ["is_element/cactus_lobes","T is not an RZ_set",T,cT];
  return false;  
 fi;

 if T = `empty/RZ` then
  reason := ["is_element/cactus_lobes","T is empty",T,cT];
  return false;  
 fi;

 return true;
end:

`is_equal/cactus_lobes` := proc(cT0,cT1)
 return `is_equal/RZ`(cT0[1],cT1[1]) and
        `is_equal/RZ_set`(cT0[2],cT1[2]);
end:

`random_element/cactus_lobes` := proc()
 local T;
 T := `empty/RZ_set`;
 while T = `empty/RZ_set` do T := `random_element/RZ_set`(); od:
 return [`random_element/RZ`(),T];
end:

`is_leq/cactus_lobes` := NULL:
`list_elements/cactus_lobes` := NULL:
`count_elements/cactus_lobes` := NULL:

`start/cactus_lobes` := (cT) -> cT[1];
`motion_set/cactus_lobes` := (cT) -> cT[2];
`speed/cactus_lobes` := (cT) -> 1/`length/RZ_set`(cT[2]);

`eval/cactus_lobes` := (cT) -> proc(t)
 local t0,c,T,n,i,u,s;

 c,T := op(cT);
 n := nops(T)/2;
 i := 1;
 u := c;
 s := 1/`length/RZ_set`(T);
 t0 := t - floor(t);
 while i <= n and T[2*i-1] <= t0 do
  u := u + s*(min(t0,T[2*i]) - T[2*i-1]);
  i := i+1;
 od: 

 u := u - floor(u);
 return u;
end:

`id/cactus_lobes` := [0,[0,1]];

`o/cactus_lobes` := proc(cT,dU)
 local c,T,d,U,n,m,sT,sU,T1,T2,n1,V,a,b,y,z,i,j,aa,bb;
 c,T := op(cT);
 d,U := op(dU);
 n := nops(T)/2;
 m := nops(U)/2;
 sT := 1/`length/RZ_set`(T);
 sU := 1/`length/RZ_set`(U);
 T1 := `unroll/RZ_set`(T);
 n1 := nops(T1)/2;
 V := NULL;
 y := d;
 for i from 1 to m do
  a := U[2*i-1];
  b := U[2*i];
  z := y + sU * (b - a);
  T2 := (T1 -~ y)/~sU +~ a; 
  for j from 1 to n1 do
   if T2[2*j] >= a and T2[2*j-1] <= b then
    aa := max(T2[2*j-1],a);
    bb := min(T2[2*j],b);
    if aa < bb then 
     V := V,aa,bb;
    fi;
   fi;
  od;
  y := z;
 od;

 return [`eval/cactus_lobes`(cT)(d),[V]];
end:

`source_shift/cactus_lobes` := (t) -> proc(cT)
 local c,d,T,U;
 c,T := op(cT);
 U := `shift/RZ_set`(t)(T);
 d := `eval/cactus_lobes`(cT)(-t);
 return [d,U];
end:

`target_shift/cactus_lobes` := (t) -> proc(cT)
 local c,d,T;
 c,T := op(cT);
 d := c+t;
 d := d - floor(d);
 return [d,T];
end:

`plot/cactus_lobes` := proc(cT)
 local c,T,L,x,y,z,a,b,n,i,s,A;
 c,T := op(cT);
 L := NULL;
 if T[1] > 0 then
  L := L,[[0,c],[T[1],c]];
 fi;
 y := c;
 n := nops(T)/2;
 s := 1/`length/RZ_set`(T);
 for i from 1 to n do
  a := T[2*i-1];
  b := T[2*i];
  z := y + s * (b-a);
  if z <= 1 then
   L := L,[[a,y],[b,z]];
   y := z;
  else
   x := a + (1 - y)/s;
   L := L,[[a,y],[x,1]],[[x,0],[b,z-1]];
   y := z-1;
  fi;
  x := `if`(i < n,T[2*i+1],1);
  if b < x then
   L := L,[[b,y],[x,y]];
  fi;
 od;

 A := args[2..-1];
 return
  display(map(u -> line(u[1],u[2],A),[L]),scaling=constrained,axes=none);
end:

`full_plot/cactus_lobes` := proc(cT)
 display(
  `plot/cactus_lobes`(cT),
  seq(line([x,0],[x,1],colour=red),x in [0,1]),
  seq(line([x,0],[x,1],colour=red,linestyle=dot),x in cT[2]),
  line([0,0],[1,0],colour=blue),
  line([0,1],[1,1],colour=blue),
  line([0,cT[1]],[1,cT[1]],colour=green,linestyle=dash)
 );
end:

