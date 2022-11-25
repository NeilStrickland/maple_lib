make_GL3_2 := proc()
 global GL3_2;
 local G,L,E,f,n,i,j,k,g,h,t,a0,a1,a2,ap,am,
   A3,B3,A4,B4,A6,B6,A6o,B6o,cci,id3,WW,WWi;
 
 G := table():

 G["group_order"] := 168;
 
 L := [[]]:
 for i from 1 to 9 do
  L := [seq(seq([op(t),j],j=0..1),t in L)];
 od:

 # Strange order ensures that 1 comes first, followed by other
 # upper unitriangular matrices.
 f := (u) -> Matrix([[u[7],u[5],u[6]],
                     [u[1],u[8],u[4]],
		     [u[3],u[2],u[9]]]);
 L := select(u -> mods(Determinant(f(u)),2) <> 0,L);
 n := nops(L);
 E := map(f,L);
 
 G["elements"] := E;
 
 G["index"] := table():
 for i from 1 to n do G["index"][convert(E[i],listlist)] := i; od:

 G["a"] := <<1|1|0>,<0|1|0>,<0|0|1>>;
 G["b"] := <<0|0|1>,<1|0|0>,<0|1|0>>;
 G["al"] := convert(G["a"],listlist);
 G["bl"] := convert(G["b"],listlist);
 G["ai"] := G["index"][G["al"]];
 G["bi"] := G["index"][G["bl"]];
 G["gens_rule"] := {A = G["a"], B = G["b"]};
 G["rels"] := [[A$2],[B$3],map(op,[[A,B]$7]),map(op,[[A,B,A,B,B]$4])];
 
 G["id"] := IdentityMatrix(3);
 G["o"] := (u,v) -> map(mods,u . v,2);
 G["inv"] := (u) -> map(mods,1 / u,2);
 G["conj"] := (u,v) -> map(mods,u . v . (1/u),2);

 G["word_to_matrix"] := proc(w::list,ab_,red_)
  local n,T,g,x,id,red;

  if nargs > 1 then
   T := table([A = ab_[1],B = ab_[2]]);
   n := Dimension(ab_[1])[1];
   id := IdentityMatrix(n);
   if nargs > 2 then
    red := red_;
   else
    red := ((t) -> t);
   fi;
  else
   T := table([A = G["a"],B = G["b"]]);
   n := 3;
   id := IdentityMatrix(3);
   red := ((t) -> modp(t,2));
  fi;
  g := id;
  for x in w do g := map(red,g . T[x]); od:
  return g;
 end:

 G["check_representation"] := proc(AB,red_)
  local T,n,id,red,w,g,x;
  if not(type(AB,[Matrix,Matrix])) then 
   return false;
  fi;
  n := Dimension(AB[1])[1];
  if not([Dimension(AB[1])]=[n,n] and 
	 [Dimension(AB[2])]=[n,n]) then 
   return false;
  fi; 
  id := IdentityMatrix(n);

  if nargs > 1 then red := red_ else red := ((t) -> t); fi;

  for w in G["rels"] do 
   if not(Equal(G["word_to_matrix"](w,AB,red),id)) then 
    return [false,w,g];
   fi;
  od:

  return true;
 end:

 G["character_of_representation"] := proc(AB,red_)
  local red,w,g;
  if nargs > 1 then 
   red := red_;
  else
   red := ((t) -> t);
  fi;
  return map(w -> red(Trace(G["word_to_matrix"](w,AB,red))),
	     G["conjugacy_class_words"]);
 end:


 G["o_table"] := table();
 G["inv_table"] := table();
 G["conj_table"] := table();

 for i from 1 to n do
  g := G["elements"][i];
  G["inv_table"][i] := G["index"][convert(G["inv"](g),listlist)];

  for j from 1 to n do
   h := G["elements"][j];
   G["o_table"][i,j] := G["index"][convert(G["o"](g,h),listlist)];
   G["conj_table"][i,j] := G["index"][convert(G["conj"](g,h),listlist)];
  od:
 od:

 WW := table([1=[],G["ai"]=[A],G["bi"]=[B]]):
 WWi := map(op,[indices(WW)]):
 while nops(WWi) < G["group_order"] do 
  for i in WWi do 
   j := G["o_table"][i,G["ai"]];
   if not(member(j,WWi)) then 
    WW[j] := [op(WW[i]),A];
   fi;
   j := G["o_table"][i,G["bi"]];
   if not(member(j,WWi)) then 
    WW[j] := [op(WW[i]),B];
   fi;
  od:
  WWi := map(op,[indices(WW)]):
 od:

 G["word"] := eval(WW);

 G["ee"] := convert(IdentityMatrix(n),listlist);

 G["ring_id"] := G["ee"][1];
 
 G["antipode"] := proc(u)
  local n,M,w,i,j;
  n := G["group_order"];
  M := eval(GL3_2["inv_table"]);
  w := [seq(u[M[i]],i=1..n)];
  return w;
 end:
 
 G["convolve"] := proc(u,v)
  local n,J,M,w,i,j,ii;
  n := G["group_order"];
  J := eval(GL3_2["inv_table"]);
  M := eval(GL3_2["o_table"]);
  w := [0$n];
  for i from 1 to n do
   if u[i] <> 0 then
    ii := J[i];
    w := w +~ [seq(u[i] * v[M[ii,j]],j=1..n)];
   fi;
  od;

  return w;
 end:


 G["borel_elements"] :=
   [seq(seq(seq(Matrix([[1,i,j],[0,1,k],[0,0,1]]),i=0..1),j=0..1),k=0..1)]:
 G["borel_indices"] :=
   map(b -> G["index"][convert(b,listlist)],G["borel_elements"]);
 G["borel_sum"] := [0$G["group_order"]]:
 for i in G["borel_indices"] do
  G["borel_sum"] := G["borel_sum"] +~ G["ee"][i]:
 od:

 G["coxeter_elements"] := map(permutation_matrix,combinat[permute](3)):
 G["coxeter_indices"] := map(w -> G["index"][convert(w,listlist)],G["coxeter_elements"]):
 G["signed_coxeter_sum"] := [0$G["group_order"]]:
 for i in G["coxeter_indices"] do
  G["signed_coxeter_sum"] := G["signed_coxeter_sum"] +~ Determinant(E[i]) *~ G["ee"][i]:
 od:

 G["steinberg_idempotent"] :=
  G["convolve"](G["signed_coxeter_sum"], G["borel_sum"]) /~ 21;

 id3 := G["id"];
 
 G["conjugacy_classes"] := [
  select(g -> Equal(g,id3),E),
  select(g -> Equal(modp(g^2,2),id3) and not(Equal(g,id3)),E),
  select(g -> Equal(modp(g^3,2),id3) and not(Equal(g,id3)),E),
  select(g -> Equal(modp(g^4,2),id3) and not(Equal(modp(g^2,2),id3)),E),
  select(g -> Equal(modp(g^3 + g + id3,2),0 * id3),E),
  select(g -> Equal(modp(g^3 + g^2 + id3,2),0 * id3),E)
 ];

 G["conjugacy_class_indices"] := map(
  C -> map(g -> G["index"][convert(g,listlist)],C),
  G["conjugacy_classes"]
 );

 G["conjugacy_class_words"] := [
  [],[A],[B],[A,B,A,B,B],[A,B,B],[A,B]
 ];


 cci := Vector([0$G["group_order"]]);
 for i from 1 to 6 do
  for j in G["conjugacy_class_indices"][i] do
   cci[j] := i;
  od;
 od:
 cci := convert(cci,list):
 G["conjugacy_class_index"] := cci;
 
 G["redu"] := (x) -> rem(x,1+u+u^2+u^3+u^4+u^5+u^6,u);
 G["frobenius"] := (x) -> G["redu"](subs(u = u^2,x));
 G["bar"] := (x) -> G["redu"](subs(u = u^6,x));
 G["invu"] := proc(x)
  local y,m,i,rels,sol;
  y := add(m[i] * u^i,i=0..5);
  rels := {coeffs(redu(x*y-1),u)};
  sol := solve(rels,{seq(m[i],i=0..5)});
  y := subs(sol,y);
  return y;
 end:

 a0 := (2*(u^3+u^4)-(u^2+u^5)-2)/7;
 a1 := G["frobenius"](a0);
 a2 := G["frobenius"](a1);
 ap := u + u^2 + u^4;
 am := u^3 + u^5 + u^6;
 G["a0"] := a0; G["a1"] := a1; G["a2"] := a2; G["ap"] := ap; G["am"] := am;

 G["cyclotomic_rels"] := [
  coeffs(expand(t^3 + t^2 - 1/7 - (t - a0)*(t - a1)*(t - a2)),t),
  (2 * ap + 1)^2 + 7,  
  (2 * am + 1)^2 + 7,
  (ap - am)^2 + 7,
  ap + am + 1,
  ap * am - 2
 ];
 
 A3 := <<a0|u^3*a2|u^2*a1>,<u^4*a2|a1|u^6*a0>,<u^5*a1|u*a0|a2>>:
 B3 := <<u^6*a0|u^2*a2|u*a1>,<u^2*a2|u^5*a1|u^4*a0>,<u*a1|u^4*a0|u^3*a2>>:
 A4 := map(G["bar"],A3):
 B4 := map(G["bar"],B3):
 A6 := Matrix([
  [ 1, 0, 0, 0, 0, 0, 0, 0],
  [ 0, 1, 0, 0, 0, 0, 0, 0],
  [ 0, 0, 0, 1, 0, 0, 0, 0],
  [ 0, 0, 1, 0, 0, 0, 0, 0],
  [ 1, 0,-1,-1,-1, 0, 0, 0],
  [ 1, 1, 0, 0, 0,-1, 0, 0],
  [ 0, 0, 0, 0, 0, 0, 0, 1],
  [ 0, 0, 0, 0, 0, 0, 1, 0]
 ]);
 B6 := Matrix([
  [ 0, 0, 0, 1, 0, 0, 0, 0],
  [ 0, 0, 1, 0, 0, 0, 0, 0],
  [ 0, 0, 0, 0, 0, 0, 1, 0],
  [ 0, 0, 0, 0, 0, 1, 0, 0],
  [ 1, 0,-1, 0,-1,-1,-1, 1],
  [ 1, 0, 0, 0, 0, 0, 0, 0],
  [ 0, 1, 0, 0, 0, 0, 0, 0],
  [ 1, 0,-1,-1,-1, 0, 0, 0]
 ]); 

 A6o := DiagonalMatrix([1$4,(-1)$4]);
 B6o := Matrix([
  [         0, -sqrt(3)/4,       -3/4,         0,   sqrt(2)/4,           0,            -1/8,  -sqrt(7)/8],
  [         0,        1/4,  sqrt(3)/4,         0,   sqrt(6)/4,           0,      -sqrt(3)/8, -sqrt(21)/8],
  [      -1/4,          0,          0, sqrt(7)/4,  -sqrt(2)/8,  sqrt(14)/8,             3/8,  -sqrt(7)/8],
  [-sqrt(7)/4,          0,          0,      -1/4, -sqrt(14)/8,  -sqrt(2)/8,      -sqrt(7)/8,        -3/8],
  [         0,  sqrt(6)/8, -sqrt(2)/8,         0,           0,   sqrt(7)/4, -(7*sqrt(2))/16, sqrt(14)/16],
  [         0, sqrt(42)/8,-sqrt(14)/8,         0,           0,        -1/4,     sqrt(14)/16, -sqrt(2)/16],
  [      -1/4,          0,          0, sqrt(7)/4,   sqrt(2)/8, -sqrt(14)/8,            -3/8,   sqrt(7)/8],
  [ sqrt(7)/4,          0,          0,       1/4, -sqrt(14)/8,  -sqrt(2)/8,      -sqrt(7)/8,        -3/8]
 ]):

 G["representations"] := [
  [IdentityMatrix(1),IdentityMatrix(1)],
  [A3,B3],
  [A4,B4],
  [reduced_permutation_matrix([3,2,1,4,7,6,5]),
   reduced_permutation_matrix([2,4,6,1,3,5,7])],
  [reduced_permutation_matrix([2,1,4,3,6,5,8,7]),
   reduced_permutation_matrix([1,7,5,3,4,2,6,8])],
  [A6,B6]
 ]:

 G["orthogonal_representations"] := [
  G["representations"][1],
  G["representations"][2],
  G["representations"][3],
  false,
  false,
  [A6o,B6o]
 ]:

 G["characters"] := [
  [1,1,1,1,1,1],
  [3,-1,0,1,ap,am],
  [3,-1,0,1,am,ap],
  [6,2,0,0,-1,-1],
  [7,-1,1,-1,0,0],
  [8,0,-1,0,1,1]
 ];

 G["full_characters"] := [
  seq([seq(G["characters"][i][G["conjugacy_class_index"][j]],j=1..G["group_order"])],i=1..6)
 ]:

 G["central_idempotents"] := [
  seq([seq(
   G["characters"][i][G["conjugacy_class_index"][G["inv_table"][j]]]
   * G["characters"][i][1]/G["group_order"]
  ,j=1..G["group_order"])],i=1..6)]:


 G["generated_subgroup"] := proc(gens)
  local M,H,i,g1,g2;
  M := eval(G["o_table"]);
  H := {1,op(gens)};
  for i from 1 to 5 do 
   H := {seq(seq(M[g1,g2],g2 in H),g1 in H)};
  od:
  return H;
 end:

 # The numbers appearing in subgroup names are the orders of the subgroups,
 # except that H22a and H22b are isomorphic to C2 x C2 and so have order 4.
 # Subgroups with a suffix x or y are conjugate to the corresponding group
 # with no suffix.  Pairs of subgroups with suffices a and b are isomorphic
 # but not conjugate.
 
 G["subgroup_gens"] := table([
  "H1" = {},
  "H2" = {2},
  "H2x" = {4},
  "H2y" = {6},
  "H3" = {11},
  "H3x" = {42},
  "H3y" = {79},
  "H22a" = {2,3},
  "H22b" = {2,5},
  "H4" = {7},
  "H6" = {2,11},
  "H6x" = {6,42},
  "H6y" = {4,79},
  "H7" = {28},
  "H8" = {3,7},
  "H12a" = {2,38},
  "H12b" = {2,76},
  "H21" = {11,28},
  "H24a" = {7,38},
  "H24b" = {7,76},
  "H168" = {2,28}
 ]);

 G["subgroup_orders"] := table([
  "H1" = 1,
  "H2" = 2, "H2x" = 2, "H2y" = 2,
  "H3" = 3, "H3x" = 3, "H3y" = 3,
  "H22a" = 4, "H22b" = 4, "H4" = 4,
  "H6" = 6, "H6x" = 6, "H6y" = 6,
  "H7" = 7,
  "H8" = 8,
  "H12a" = 12, "H12b" = 12,
  "H21" = 21,
  "H24a" = 24, "H24b" = 24,
  "H168" = 168
 ]);

 G["subgroup_names"] := map(op,[indices(G["subgroup_gens"])]);
 
 G["subgroups"] := table():

 for i in G["subgroup_names"] do
  G["subgroups"][i] := G["generated_subgroup"](G["subgroup_gens"][i]);
 od:

 G["subgroup_inclusions"] := [
  ["H2", "H22a"],
  ["H2", "H22b"],
  ["H2", "H4"],
  ["H2x", "H6y"],
  ["H2y", "H6x"],
  ["H3", "H6"],
  ["H3x", "H6x"],
  ["H3y", "H6y"],
  ["H3", "H21"],
  ["H3x", "H21"],
  ["H3y", "H21"],
  ["H22a", "H12a"],
  ["H22b", "H12b"],
  ["H4", "H8"],
  ["H6x", "H24a"],
  ["H6y", "H24b"],
  ["H7", "H21"],
  ["H8", "H24a"],
  ["H8", "H24b"],
  ["H12a", "H24a"],
  ["H12b", "H24b"]
 ];

 G["subgroup_conjugations"] := [
  [33,"H2","H2x"],
  [73,"H2","H2y"],
  [88,"H3","H3x"],
  [42,"H3","H3y"],
  [88,"H6","H6x"],
  [42,"H6","H6y"]
 ];

 GL3_2 := eval(G);
 return(eval(G));
end:

check_GL3_2 := proc(G_)
 local G,C,w,ci,i,j,n,ok,AB;

 if nargs > 0 then G := eval(G_); else G := eval(make_GL3_2()); fi;

 _ASSERT(
  `and`(op(map(w -> Equal(G["word_to_matrix"](w),G["id"]),G["rels"]))),
  "relations in a and b are satisfied"
 );

 _ASSERT(
  sort(map(op,G["conjugacy_class_indices"])) = [seq(i,i=1..G["group_order"])],
  "conjugacy classes give a partition"
 );

 _ASSERT(
  `and`(op(
    map(C -> evalb({seq(G["conj_table"][i,C[1]],i=1..G["group_order"])} = {op(C)}),
    G["conjugacy_class_indices"])
  )),
  "conjugacy classes are conjugacy classes"
 );

 ok := true;
 for i from 1 to nops(G["conjugacy_classes"]) do 
  C := G["conjugacy_class_indices"][i];
  w := G["conjugacy_class_words"][i];
  j := G["index"][convert(G["word_to_matrix"](w),listlist)];
  if not(member(j,C)) then
   ok := false; break;
  fi;
 od:

 _ASSERT(ok,"conjugacy class words have the right class");

 _ASSERT(
  {op(map(G["redu"],G["cyclotomic_rels"]))} = {0} and
  abs(evalf[12](subs(u = exp(2*Pi*I/7),G["ap"] - (-1+sqrt(-7))/2))) < 10.^(-10) and 
  abs(evalf[12](subs(u = exp(2*Pi*I/7),G["am"] - (-1-sqrt(-7))/2))) < 10.^(-10),
  "relations in the cyclotomic field"
 );

 ok := true;
 for i from 1 to nops(G["representations"]) do 
  AB := G["representations"][i];
  if AB <> false and not(G["check_representation"](AB,G["redu"])) then
   ok := false; break;
  fi;
 od:

 _ASSERT(
  ok,
  "representations preserve relations"
 );
 
 ok := true;
 for i from 1 to nops(G["representations"]) do 
  AB := G["representations"][i];
  if AB <> false and
     map(G["redu"],G["character_of_representation"](AB,G["redu"]) -~ 
         G["characters"][i]) <> [0$6] then
   ok := false; break;
  fi;
 od:

 _ASSERT(
  ok,
  "representations have claimed characters"
 );
 
 _ASSERT(
  `and`(seq(evalb(nops(G["subgroups"][n]) = G["subgroup_orders"][n]),n in G["subgroup_names"])),
  "subgroup orders are correct"
 );

 _ASSERT(
  `and`(op(map(u -> evalb(G["subgroups"][u[1]] minus G["subgroups"][u[2]] = {}),
        G["subgroup_inclusions"]))),
  "subgroup inclusions are correct"
 );

 _ASSERT(
  `and`(op(
    map(u -> evalb(map(i -> G["conj_table"][u[1],i],G["subgroups"][u[2]]) = G["subgroups"][u[3]]),
        G["subgroup_conjugations"])
  )),
  "subgroup conjugations are correct"
 );
 
 ci := G["central_idempotents"]:

 _ASSERT(
  `and`(seq(evalb(map(G["redu"],expand(G["convolve"](ci[i],ci[i]))) = map(G["redu"],ci[i])),i=1..6)),
  "central idempotents are idempotent"
 );

 
end:

save_GL3_2 := proc()
 if not(type(GL3_2,table)) then
  make_GL3_2();
 fi;

 save(GL3_2,cat(data_dir,"/GL3_2.m"));
end:

save_GL3_2 := proc()
 if not(type(GL3_2,table)) then
  make_GL3_2();
 fi;

 save(GL3_2,cat(data_dir,"/GL3_2.m"));
end:

