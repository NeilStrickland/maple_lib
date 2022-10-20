dunce_complex := proc()
 local T,T0,V,V0,F,F0,v,d;
 
 T := table();
 T0 := table();
 
 V := {0,1,2,3,4,5,6,7,8,9};
 V0 := {0.1,0.2,0.3,1.1,1.2,1.3,2.1,2.2,2.3,3,4,5,6,7,8,9};

 T["dim"] := 2;
 T0["dim"] := 2;
 
 T["vertices"] := V;
 T0["vertices"] := V0;
 
 F0 := {
  {0.1,3,4},{0.1,1.1,4},{1.1,4,5},{1.1,2.1,5},{0.2,2.1,5},
  {0.2,5,6},{0.2,1.2,6},{1.2,6,7},{1.2,2.2,7},{0.3,2.2,7},
  {0.3,7,8},{0.3,2.3,8},{1.3,2.3,8},{1.3,3,8},{0.1,1.3,3},
  {3,4,9},{4,5,9},{5,6,9},{6,7,9},{7,8,9},{3,8,9}
 };

 F := map(u -> map(round,u),F0);
 
 T["max_simplices"] := F;
 T0["max_simplices"] := F0;

 T["all_simplices"] := 
   map(f -> op(combinat[powerset](f)),F) minus {{}}:

 T0["all_simplices"] := 
   map(f -> op(combinat[powerset](f)),F0) minus {{}}:

 T["simplices"] := table():
 T0["simplices"] := table():

 for d from 0 to 4 do 
  T["simplices"][d] := select(u -> nops(u) = d+1,T["all_simplices"]);
  T0["simplices"][d] := select(u -> nops(u) = d+1,T0["all_simplices"]);
 od:

 T0["embedding_dim"] := 2;
 T0["embedding3"] := table([
  0.1 = [6,0,0], 1.1 = [4,2,0], 2.1 = [2,4,0],
  0.2 = [0,6,0], 1.2 = [0,4,2], 2.2 = [0,2,4],
  0.3 = [0,0,6], 2.3 = [2,0,4], 1.3 = [4,0,2],
  3 = [3,1,2], 4 = [3,2,1], 5 = [2,3,1], 6 = [1,3,2], 7 = [1,2,3], 8 = [2,1,3],
  9 = [2,2,2]
 ]);

 T0["embedding"] := table():
 
 for v in V0 do
  T0["embedding"][v] := simplex_embedding(T0["embedding3"][v] /~ 6);
 od:

 T0["plot"] := `plot/raw_simplicial_complex`(F0,2,T0["embedding"]);

 T["net"] := eval(T0);
 return eval(T);
end:

dunce_complex_old := proc()
 local T,T0,V,V0,F,F0,v,d;
 
 T := table();
 T0 := table();
 
 V := {0,1,2,3,4,5,6,7,8,9};
 V0 := {0.1,0.2,0.3,1.1,1.2,1.3,2.1,2.2,2.3,3,4,5,6,7,8,9};

 T["dim"] := 2;
 T0["dim"] := 2;
 
 T["vertices"] := V;
 T0["vertices"] := V0;
 
 F0 := {
  {0.1,1.1,7},{1.1,2.1,7},{2.1,7,8},{0.2,2.1,8},{0.2,3,8},
  {0.2,1.2,3},{1.2,2.2,3},{2.2,3,4},{0.3,2.2,4},{0.3,4,5},
  {0.3,1.3,5},{1.3,2.3,5},{2.3,5,6},{0.1,2.3,6},{0.1,6,7},
  {3,4,9},{4,5,9},{5,6,9},{6,7,9},{7,8,9},{3,8,9}
 };

 F := map(u -> map(round,u),F0);
 
 T["max_simplices"] := F;
 T0["max_simplices"] := F0;

 T["all_simplices"] := 
   map(f -> op(combinat[powerset](f)),F) minus {{}}:

 T0["all_simplices"] := 
   map(f -> op(combinat[powerset](f)),F0) minus {{}}:

 T["simplices"] := table():
 T0["simplices"] := table():

 for d from 0 to 4 do 
  T["simplices"][d] := select(u -> nops(u) = d+1,T["all_simplices"]);
  T0["simplices"][d] := select(u -> nops(u) = d+1,T0["all_simplices"]);
 od:

 T0["embedding_dim"] := 2;
 T0["embedding3"] := table([
  0.1 = [6,0,0], 0.2 = [0,6,0], 0.3 = [0,0,6],
  1.1 = [4,2,0], 1.2 = [0,4,2], 1.3 = [2,0,4],
  2.1 = [2,4,0], 2.2 = [0,2,4], 2.3 = [4,0,2],
  3 = [1,3,2], 4 = [1,2,3], 5 = [2,1,3], 6 = [3,1,2], 7 = [3,2,1], 8 = [2,3,1],
  9 = [2,2,2]
 ]);

 T0["embedding"] := table():
 
 for v in V0 do
  T0["embedding"][v] := simplex_embedding(T0["embedding3"][v] /~ 6);
 od:

 T0["plot"] := `plot/raw_simplicial_complex`(F0,2,T0["embedding"]);

 T["net"] := eval(T0);
 return eval(T);
end:
