SL2_11 := table():

SL2_11["elements"] := {
 seq(seq(seq(seq(<<e*a|b>,<c|mods(e*(1+b*c)/a,11)>>,c=-5..5),b=-5..5),a=1..5),e in {-1,1}),
 seq( seq(seq(<<0|e*b>,<mods(-e/b,11)|d>>,d=-5..5),b=1..5),e in {-1,1})
}:

SL2_11["projective_line"] := {seq(i,i=-5..5),infinity};

SL2_11["action"] := proc(g,u)
 local a,b,c,d,nn,dd;

 a := g[1,1]; b := g[1,2];
 c := g[2,1]; d := g[2,2];
 if u = infinity then
  if c = 0 then
   return infinity;
  else
   return mods(a/c,11);
  fi;
 else
  nn := mods(a * u + b,11);
  dd := mods(c * u + d,11);
  if dd = 0 then
   return infinity;
  else
   return mods(nn/dd,11);
  fi;
 fi;
end:

SL2_11["first_hexad"] := {seq(mods(i^2,11),i=0..5)};

SL2_11["hexads"] := 
 {seq(map2(SL2_11["action"],g,SL2_11["first_hexad"]),g in SL2_11["elements"])};

# `is_element/steiner_systems`(SL2_11["projective_line"])(5,6)(SL2_11["hexads"]);