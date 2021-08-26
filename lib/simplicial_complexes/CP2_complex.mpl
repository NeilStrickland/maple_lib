# This file sets up the 15-vertex triangulation of CP^2 introduced by
# Gaifullin in "A minimal triangulation of complex projective plane ..."
# (arxiv:0904.4222)

with(GroupTheory):

CP2_complex := proc()
 local T,V,F,p,a,b,d,s,S,om,ob,rt,
  id_S,o_S,inv_S,act_S,eq_S,eq_X,v,ix_v,i;

 T := table():

 # We take the vertices to be 1,...,15
 # In Gaifullin's presentation, the vertex set is
 # {transposition pairs} union {1,2,3,4} x {1,2,3}
 # Gaifullin's (i,j) is our 1 + 3 * (i-1) + (j-1)
 # The transposition pairs are our vertices 13-15.

 V := {seq(i,i=1..15)}:

 T["vertices"] := V;

 F := NULL:

 # This table encodes the three transposition pairs on {0,1,2,3}
 p := table():
 p[1,0] := 1; p[1,1] := 0; p[1,2] := 3; p[1,3] := 2;
 p[2,0] := 2; p[2,1] := 3; p[2,2] := 0; p[2,3] := 1;
 p[3,0] := 3; p[3,1] := 2; p[3,2] := 1; p[3,3] := 0;
 
 for a from 1 to 3 do 
  for b[0] from 0 to 2 do
   for b[1] from 0 to 2 do 
    for b[2] from 0 to 2 do
     for b[3] from 0 to 2 do
      if b[0] <> b[p[a,0]] and
	 b[1] <> b[p[a,1]] and
	 b[2] <> b[p[a,2]] and
	 b[3] <> b[p[a,3]] then
       F := F,{b[0]+1,b[1]+4,b[2]+7,b[3]+10,a+12};
      fi;
     od:
    od:
   od:
  od:
 od:
 F := {F}:

 T["max_simplices"] := F;
 T["all_simplices"] := 
   map(f -> op(combinat[powerset](f)),F) minus {{}}:

 T["simplices"] := table():
 for d from 0 to 4 do 
  T["simplices"][d] := select(u -> nops(u) = d+1,T["simplices"]);
 od:

 s := table():
 T["s"] := eval(s);

 s[0] := Perm([]):
 s[1] := Perm([[ 1, 4],[ 2, 5],[ 3, 6],[14,15]]):
 s[2] := Perm([[ 4, 7],[ 5, 8],[ 6, 9],[13,14]]):
 s[3] := Perm([[ 7,10],[ 8,11],[ 9,12],[14,15]]):
 s[4] := Perm([[ 1, 2],[ 4, 5],[ 7, 8],[10,11]]):
 s[5] := Perm([[ 2, 3],[ 5, 6],[ 8, 9],[11,12]]):

 T["S4"] := Group(s[1],s[2],s[3]);
 T["S3"] := Group(s[4],s[5]);
 T["G"]  := Group(seq(s[i],i=1..5));

 S := table():
 T["S"] := eval(S);

 om := exp( 2*Pi*I/3);
 ob := exp(-2*Pi*I/3);
 rt := sqrt(3);

 S[0] := [ 1,[[ 1, 0, 0],[ 0, 1, 0],[ 0, 0, 1]]]:
 S[1] := [-1,[[ 0, 1, 0],[ 1, 0, 0],[ 0, 0, 1]]];
 S[2] := [-1,[[ 1, 0, 0],[ 0, 0, 1],[ 0, 1, 0]]];
 S[3] := [-1,[[ 0,-1, 0],[-1, 0, 0],[ 0, 0, 1]]];
 S[4] := [-1,[[ 1, 0, 0],[ 0, 1, 0],[ 0, 0, 1]]];
 S[5] := [-1,[[ 1, 0, 0],[ 0,om, 0],[ 0, 0,ob]]];

 id_S := S[0];

 o_S := proc(u,v)
  local m,n,mn,A,B,AB;
  m,A := op(u);
  n,B := op(v);
  mn := m*n;
  if n = -1 then A := conjugate(A); fi;
  AB := convert(Matrix(A) . Matrix(B),listlist);
  AB := simplify(expand(rationalize(AB)));
  return [mn,AB]; 
 end:

 inv_S := proc(u) 
  local m,A;
  m,A := op(u);
  if m = -1 then A := conjugate(A); fi;
  A := convert(1/Matrix(A),listlist);
  A := simplify(expand(rationalize(A)));
  return [m,A];
 end:

 act_S := (u) -> proc(x)
  local y;
  y := Vector(x);
  y := simplify(convert(Matrix(u[2]) . y,list));
  if u[1] = -1 then y := map(conjugate,y); fi;
  return y;
 end:

 eq_S := proc(u,v)
  local w;
  if u[1] <> v[1] then return false; fi;
  w := o_S(u,inv_S(v));
  if w[2][1,1] = 0 then return false; fi;
  w := [w[1],map(simplify,map(expand,w[2] /~ w[2][1,1]))];
  return evalb(w = id_S);
 end:

 eq_X := proc(u,v)
  local i,j;
  `and`(seq(seq(evalb(simplify(u[i]*v[j]-u[j]*v[i])=0),j=i+1..3),i=1..2));
 end:

 v := table([
   1 = [  1,-om,-ob],
   2 = [  1,-ob,-om],
   3 = [  1, -1, -1],
   4 = [  1,-om, ob],
   5 = [  1,-ob, om],
   6 = [  1, -1,  1],
   7 = [  1, om,-ob],
   8 = [  1, ob,-om],
   9 = [  1,  1, -1],
  10 = [  1, om, ob],
  11 = [  1, ob, om],
  12 = [  1,  1,  1],
  13 = [  0,  0, rt],
  14 = [  0, rt,  0],
  15 = [ rt,  0,  0]
 ]):

 T["projective_embedding"] := eval(v);

 ix_v := proc(u)
  local i;
  for i from 1 to 15 do
   if eq_X(u,v[i]) then return i; fi;
  od;
  return FAIL;
 end:

 return eval(T):
end: