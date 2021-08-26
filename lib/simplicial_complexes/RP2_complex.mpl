RP2_net_complex := proc()
 local T,rt,tau,i;

 T["vertices"] := {seq(i,i=1..9)};
 T["faces"] := {{1,2,3},{1,2,5},{1,3,9},{1,4,5},{1,4,9},{2,3,7},{2,5,6},{2,6,7},{3,7,8},{3,8,9}};
 T["max_simplices"] := T["faces"];
 
 rt := sqrt(3);
 tau := (1+sqrt(5))/2;

 T["flat_embedding"] := table([
  1 = [ 1/2, 0   ],
  2 = [-1/4, rt/4],
  3 = [-1/4,-rt/4],
  4 = [ 1  , 0   ],
  5 = [ 1/2, rt/2],
  6 = [-1/2, rt/2],
  7 = [-1  , 0   ],
  8 = [-1/2,-rt/2],
  9 = [ 1/2,-rt/2]
 ]):

 T["icosahedron_embedding"] := table([
   1 = [   0,   1, tau],
   2 = [ tau,   0,   1],
   3 = [   1, tau,   0],
   4 = [-tau,   0,   1],
   5 = [   0,  -1, tau],
   6 = [   1,-tau,   0],
   7 = [ tau,   0,  -1],
   8 = [   0,   1,-tau],
   9 = [  -1, tau,   0]
 ]):

 T["flat_plot"] :=
   `plot/simplicial_complex`(T["vertices"])(T["faces"],2,T["flat_embedding"]);

 T["icosahedron_plot"] :=
   `plot/simplicial_complex`(T["vertices"])(T["faces"],2,T["icosahedron_embedding"]);

 return eval(T);
end:

RP2_complex := proc()
 local T0,T,i;

 T0 := RP2_net_complex();
 T["vertices"] := {seq(i,i=1..6)};
 T["faces"] := subs({7=4,8=5,9=6},T0["faces"]);
 T["max_simplices"] := T["faces"];

 return eval(T);
end:
