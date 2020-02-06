make_alternating_five := proc()
 global alternating_five;
 local G,x2,y2,z2,x3,x5,y5,id,o,oo,inv,idm,om,oom,E,ccl,
       t0,t1,i,g,h,w,m,x,u0,u1,u2,u3,M,theta;
 
 G := table():

 x2 := [2,1,4,3,5];
 y2 := [3,4,1,2,5];
 z2 := [1,3,2,5,4];
 x3 := [2,3,1,4,5];
 x5 := [3,5,4,2,1];
 y5 := [2,3,4,5,1];

 id := [1,2,3,4,5];
 o  := (u,v) -> [seq(u[v[i]],i=1..5)];
 oo := proc()
  if   nargs = 0 then return(id);
  elif nargs = 1 then return(args[1]);
  elif nargs = 2 then return(o(args));
  else return o(args[1],oo(args[2..-1]));
  fi;
 end:
 inv := proc(g)
  local gi;
  gi := table():
  for i from 1 to 5 do gi[g[i]] := i; od;
  return [seq(gi[i],i=1..5)];
 end:
 
 G["id"] := id;
 G["o"]  := eval(o);
 G["oo"]  := eval(oo);
 G["inv"] := eval(inv);
 
 G["x2"] := x2;  G["x2c"] := convert(x2,disjcyc);
 G["y2"] := y2;  G["y2c"] := convert(y2,disjcyc);
 G["z2"] := z2;  G["z2c"] := convert(z2,disjcyc);
 G["x3"] := x3;  G["x3c"] := convert(x3,disjcyc);
 G["x5"] := x5;  G["x5c"] := convert(x5,disjcyc);
 G["y5"] := y5;  G["y5c"] := convert(y5,disjcyc);

 G["H"] := table():
 
 G["H"][ 1] := [id];
 G["H"][ 2] := [id,x2];
 G["H"][ 3] := [id,x3,o(x3,x3)];
 G["H"][ 4] := [id,x2,y2,o(x2,y2)];
 G["H"][ 5] := [id,x5,o(x5,x5),oo(x5 $ 3),oo(x5 $ 4)];
 G["H"][ 6] := [seq(seq(o(u,v),u in [id,z2]),v in G["H"][3])];
 G["H"][10] := [seq(seq(o(u,v),u in G["H"][ 2]),v in G["H"][5])];
 G["H"][12] := [seq(seq(o(u,v),u in G["H"][ 4]),v in G["H"][3])];
 G["H"][60] := [seq(seq(o(u,v),u in G["H"][12]),v in G["H"][5])];

 E := G["H"][60];
 G["elements"] := E;
 
 G["element_index"] := table();
 for i from 1 to 60 do
  G["element_index"][E[i]] := i; 
 od:

 G["gens_rule"] := {X2 = x2, Y2 = y2, Z2 = z2, X3 = x3, X5 = x5, Y5 = y5};

 # words in x2, y2, z2 for all elements
 G["words_a"] := [
 [],[X2],[Y2],[X2,Y2],[X2,Z2,Y2,Z2,X2,Z2],[Z2,Y2,Z2,X2,Z2],[Z2,Y2,Z2,X2,Z2,X2],
 [Y2,Z2,Y2,Z2,X2,Z2],[Y2,Z2,X2,Z2,Y2,Z2],[Z2,X2,Z2,Y2,Z2,Y2],[Z2,X2,Z2,Y2,Z2],
 [X2,Z2,X2,Z2,Y2,Z2],[X2,Y2,Z2,Y2],[Y2,Z2,Y2],[X2,Z2,Y2],[Z2,Y2],[X2,Y2,Z2,Y2,Z2,X2,Y2],
 [Y2,Z2,Y2,Z2,X2,Y2],[X2,Z2,Y2,Z2,X2,Y2],[Z2,Y2,Z2,X2,Y2],[X2,Y2,Z2,X2,Z2],[Y2,Z2,X2,Z2],
 [X2,Z2,X2,Z2],[Z2,X2,Z2],[X2,Y2,Z2,X2,Z2,Y2],[Y2,Z2,X2,Z2,Y2],[X2,Z2,X2,Z2,Y2],
 [Z2,X2,Z2,Y2],[X2,Y2,Z2],[Y2,Z2],[X2,Z2],[Z2],[X2,Y2,Z2,Y2,Z2,X2],[Y2,Z2,Y2,Z2,X2],
 [X2,Z2,Y2,Z2,X2],[Z2,Y2,Z2,X2],[Z2,Y2,Z2,Y2,Z2,X2,Z2],[X2,Z2,Y2,Z2,Y2,Z2,X2,Z2],
 [Z2,X2,Z2,X2,Y2],[X2,Z2,X2,Z2,X2,Y2],[Z2,X2],[X2,Z2,X2],[Y2,Z2,X2],[X2,Y2,Z2,X2],
 [X2,Z2,Y2,Z2],[Z2,Y2,Z2],[X2,Y2,Z2,Y2,Z2],[Y2,Z2,Y2,Z2],[Y2,Z2,X2,Y2],[Z2,X2,Y2,Z2],
 [Z2,X2,Y2],[X2,Z2,X2,Y2],[Z2,Y2,Z2,Y2],[X2,Z2,Y2,Z2,Y2],[Y2,Z2,Y2,Z2,Y2],
 [X2,Y2,Z2,Y2,Z2,Y2],[X2,Z2,X2,Z2,X2],[Z2,X2,Z2,X2],[X2,Y2,Z2,X2,Z2,X2],[Y2,Z2,X2,Z2,X2]];

 # words in x2, y2, x3, x5 for all elements
 G["words_b"] := [seq(seq(seq(seq([X2$i,Y2$j,X3$k,X5$l],i=0..1),j=0..1),k=0..2),l=0..4)];

 G["rels"] := [
  [X2$2],[Y2$2],[Z2$2],[X3$3],[X5$5],[Y5$5],
  map(op,[[X2,Y2]$2]),map(op,[[X2,Y2,Z2]$3]),
  map(op,[[Z2,X2,Z2,Y2]$3]),map(op,[[X2,Z2]$5]),map(op,[[Y2,Z2]$5]),
  [X3,Y2,Z2,X2,Z2,Y2,Z2],[Y5,Y2,Z2,X2,Z2,X2],[X5,Y2,X5,X5,X5,X3,X3]];

 ccl := (x) -> sort([op({seq(oo(g,x,inv(g)), g in E)})]);

 G["conjugacy_classes"] := [
  ccl(id),
  ccl(x2),
  ccl(x3),
  ccl(o(x5,x5)),
  ccl(x5)
 ];

 G["conjugacy_class_index"] := table();
 for i from 1 to 5 do
  for g in G["conjugacy_classes"][i] do
   G["conjugacy_class_index"][g] := i;
  od;
 od;

 G["element_order"] := table();

 for g in E do 
  h := g;
  i := 1;
  while h <> id do i := i + 1; h := o(g,h); od:
  G["element_order"][g] := i;
 od:
  
 t0 := (sqrt(5)+1)/2;
 t1 := (sqrt(5)-1)/2;
 
 # Dodecahedron representation

 idm := [[1,0,0],[0,1,0],[0,0,1]];
 om := (u,v) -> expand(convert(Matrix(u) . Matrix(v),listlist));
 oom := proc()
  if   nargs = 0 then return(idm);
  elif nargs = 1 then return(args[1]);
  elif nargs = 2 then return(om(args));
  else return om(args[1],oom(args[2..-1]));
  fi;
 end:

 G["idm"] := idm;
 G["om"]  := eval(om);
 G["oom"] := eval(oom);
 
 G["matrix_gens_rule"] := {
   X1 = [[ 1,0,0],[0, 1,0],[0,0, 1]],
   X2 = [[ 1,0,0],[0,-1,0],[0,0,-1]],
   Y2 = [[-1,0,0],[0,-1,0],[0,0, 1]],
   Z2 = [[t1,-t0,-1],[-t0,-1,t1],[-1,t1,-t0]] /~ 2,
   X3 = [[0,0,1],[1,0,0],[0,1,0]],
   X5 = [[t1,-t0,1],[t0,1,t1],[-1,t1,t0]] /~ 2,
   Y5 = [[t0,1,-t1],[-1,t1,-t0],[-t1,t0,1]] /~ 2
 };

 G["matrix"] := table();
 G["axis"]   := table();
 G["angle"]  := table();

 for i from 1 to 60 do
  g := E[i];
  G["matrix"][g] := oom(op(subs(G["matrix_gens_rule"],G["words_b"][i])));
  if i = 1 then
   G["axis"][g] := [0,0,0];
   G["angle"][g] := 0;
  else
   M := Matrix(G["matrix"][g]);
   u0 := convert(NullSpace(M - IdentityMatrix(3))[1],list);
   u0 := simplify(expand(rationalize(u0 /~ sqrt(add(u0[j]^2,j=1..3)))));
   u1 := [1,2,3];
   u1 := u1 -~ add(u1[j] * u0[j],j=1..3) *~ u0;
   u1 := simplify(expand(rationalize(u1)));
   u2 := [u0[2] * u1[3] - u0[3] * u1[2],
          u0[3] * u1[1] - u0[1] * u1[3],
          u0[1] * u1[2] - u0[2] * u1[1]];
   u2 := simplify(expand(rationalize(u2)));
   u3 := simplify(expand(rationalize(convert(M . Vector(u1), list))));
   
   theta := evalf(arctan(add(u3[j] * u2[j],j=1..3),add(u3[j] * u1[j],j=1..3)));
   theta := round(evalf(60 * theta / Pi)) * Pi / 60;
   
   if evalf(theta) < 0 then u0 := -~ u0; theta := -theta; fi; 
   G["axis"][g] := u0;
   G["angle"][g] := theta;
  fi;
 od;

 alternating_five := eval(G);
 return eval(G);
end:

make_alternating_five():

check_alternating_five := proc()
 local A5,f,fm,is_rot,ok,i,j,ij,g,h,gh,gm,hm,ghm0,ghm1;
 
 A5 := eval(make_alternating_five()):

 f := (u) -> A5["oo"](op(subs(A5["gens_rule"],u)));
 fm := (u) -> A5["oom"](op(subs(A5["matrix_gens_rule"],u)));

 _ASSERT(
  evalb({op(map(f,A5["rels"]))} = {A5["id"]}),
  "permutation relations");

 _ASSERT(
  evalb({op(map(fm,A5["rels"]))} = {A5["idm"]}),
  "matrix relations");

 _ASSERT(
  `and`(seq(evalb(f(A5["words_a"][i]) = A5["elements"][i]),i=1..60)),
  "words_a");

 _ASSERT(
  `and`(seq(evalb(f(A5["words_b"][i]) = A5["elements"][i]),i=1..60)),
  "words_b");

 is_rot := proc(m)
  local M,N;
  M := Matrix(m);
  if (simplify(expand(Determinant(M) - 1)) <> 0) then
   return false;
  fi;

  N := map(simplify,map(expand,Transpose(M) . M - IdentityMatrix(3)));
  if not(Equal(N,Matrix(3,3))) then return false; fi;
  return true;
 end:

 _ASSERT(
  `and`(seq(is_rot(A5["matrix"][g]),g in A5["elements"])),
  "matrices are rotations"
 );

 ok := true;
 for i from 1 to 60 do 
  for j from 1 to 60 do 
   g := A5["elements"][i];
   h := A5["elements"][j];
   gh := A5["o"](g,h);
   ij := A5["element_index"][gh];
   gm := A5["matrix"][g];
   hm := A5["matrix"][h];
   ghm0 := A5["matrix"][gh];
   ghm1 := A5["om"](gm,hm);
   if ghm0 <> ghm1 then ok := false; break; fi;
  od:
  if not(ok) then break; fi;
 od:

 _ASSERT(ok,"matrix representation is a homomorphism");
end: