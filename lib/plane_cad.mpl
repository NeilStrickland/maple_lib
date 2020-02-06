# This is supposed to be a toy 2D model for issues that arise in
# computational geometry for computer aided design.
# We work everywhere in the real projective plane, and consider
# only straight lines and conic curves and segments thereof.
# This is supposed to make everything nicely computable.

dp3 := (x,y) -> add(x[i]*y[i],i=1..3);
nm3 := (x) -> sqrt(add(x[i]^2,i=1..3));
xp3 := (u,v) -> [u[2]*v[3]-u[3]*v[2],
                 u[3]*v[1]-u[1]*v[3],
                 u[1]*v[2]-u[2]*v[1]];
tp3 := (u,v,w) -> Determinant(Matrix([u,v,w]));
eq3 := (u,v) -> evalb(xp3(u,v) = [0$3]);
sp3 := (u) -> [u[1]/u[3],u[2]/u[3]];

`plane_stereo/RP` := (x) -> [x[1]/x[3],x[2]/x[3]];
`plane_unstereo/RP` := (u) -> [u[1],u[2],1];

`disc_stereo/RP` := (x) -> [x[1],x[2]] *~ (signum(x[3])/nm3(x));

`disc_unstereo/RP` := (u) ->
  [u[1],u[2],sqrt(1-u[1]^2-u[2]^2)];

######################################################################

`is_element/RP_points` := proc(x)
 type(x,[numeric,numeric,numeric]);
end:

`is_leq/RP_points` := NULL:
`list_elements/RP_points` := NULL:
`count_elements/RP_points` := NULL:

`random_element/RP_points` := () -> `random_element/R`(3)();

`dist/RP_points` := proc(x,y)
 1 - add(x[i]*y[i],i=1..3)^2/add(x[i]^2,i=1..3)
end:

`is_equal/RP_points` := (x,y) -> evalb(xp3(x,y) = [0$3]);

`in_general_position/RP_points` :=
 (u,v,w) -> evalb(Determinant(Matrix([u,v,w])) = 0);

`disc_plot/point` := (x) -> point(`disc_stereo/RP`(x),args[2..-1]);

######################################################################

`is_element/RP_lines` := proc(x)
 type(x,[numeric,numeric,numeric]);
end:

`is_leq/RP_lines` := NULL:
`list_elements/RP_lines` := NULL:
`count_elements/RP_lines` := NULL:

`random_element/RP_lines` := () -> `random_element/R`(3)();

`dist/RP_lines` := proc(x,y)
 1 - add(x[i]*y[i],i=1..3)^2/add(x[i]^2,i=1..3)
end:

`is_equal/RP_lines` := (x,y) -> evalb(xp3(x,y) = [0$3]);

`in_general_position/RP_lines` :=
 (u,v,w) -> evalb(Determinant(Matrix([u,v,w])) = 0);

`track/RP_lines` := proc(x,t)
 local u,v;
 u,v := op(NullSpace(Matrix(x)));
 return (1-t) *~ u +~ t *~ v;
end:

`disc_plot/line` := proc(x)
 local u,v,w,p,t,t0,R;
 u,v := op(NullSpace(Matrix(x)));
 w := cos(Pi*t) *~ u +~ sin(Pi*t) *~ v;
 t0 := fsolve(w[3]);
 if evalf(subs(t = t0,diff(w[3],t))) > 0 then
  R := (t0 + 0.0001) .. (t0 + 0.9999);
 else 
  R := (t0 - 0.9999) .. (t0 - 0.0001);
 fi;
 p := simplify(`disc_stereo/RP`(w));
 plot([op(p),t=R],args[2..-1]);
end:

######################################################################

`is_incident/RP` := (x,y) -> evalb(add(x[i]*y[i],i=1..3) = 0);

`point_join/RP` := (x,y) -> xp3(x,y);

`line_meet/RP`  := (x,y) -> xp3(x,y);

######################################################################

`is_element/RP_conics` := proc(q)
 local c;
 if not(type(q,[numeric$6])) then
  return false;
 fi;

 # We now need to check whether the associated quadratic form
 # has one negative and two positive eigenvalues.  This works
 # out as follows.
 
 c := [-q[1]-q[2]-q[3],
       (q[1]*q[2]+q[2]*q[3]+q[3]*q[1]) - (q[4]^2+q[5]^2+q[6]^2)/4,
       (q[1]*q[4]^2+q[2]*q[5]^2+q[3]*q[6]^2-q[4]*q[5]*q[6])/4
         - q[1]*q[2]*q[3]
      ];

 if c[3] > 0 and (c[1] <= 0 or c[2] <= 0) then
  return true;
 fi;

 return false;
end:

`is_leq/RP_conics` := NULL:
`list_elements/RP_conics` := NULL:
`count_elements/RP_conics` := NULL:

`random_element/RP_conics` := proc()
 local q;

 q := `random_element/R`(6)();
 while not(`is_element/RP_conics`(q)) do
  q := `random_element/R`(6)();
 od:

 return q;
end:


`dist/RP_conics` := proc(q,r)
 sqrt(add(add((q[i]*r[j]-q[j]*r[i])^2,j=i+1..6),i=1..6)/
      (add(q[i]^2,i=1..6) * add(r[i]^2,i=1..6)));
end:

`is_equal/RP_conics` := proc(q,r)
 evalb(`dist/RP_conics`(q,r) = 0);
end:

`conic_matrix/RP` := (q) -> 
  <<q[1]|q[6]/2|q[5]/2>,<q[6]/2|q[2]|q[4]/2>,<q[5]/2|q[4]/2|q[3]>>;

`conic_unmatrix/RP` := (Q) ->
 [Q[1,1],Q[2,2],Q[3,3],2*Q[2,3],2*Q[3,1],2*Q[1,2]];

`conic_eval/RP` := (q) -> (x) ->
 q[1]*x[1]^2 + q[2]*x[2]^2 + q[3]*x[3]^2 +
 q[4]*x[2]*x[3] + q[5]*x[3]*x[1] + q[6]*x[1]*x[2];

`conic_bilin/RP` := (q) -> (x,y) ->
 (`conic_eval/RP`(q)(x +~ y) - `conic_eval/RP`(q)(x -~ y))/4; 

`conic_coeffs/RP` := (qx,x) -> [
 coeff(qx,x[1],2),
 coeff(qx,x[2],2),
 coeff(qx,x[3],2),
 coeff(coeff(qx,x[2],1),x[3],1),
 coeff(coeff(qx,x[3],1),x[1],1),
 coeff(coeff(qx,x[1],1),x[2],1)
];

`disc_implicitplot/conic` := proc(q)
 local u,v,qq;
 
 qq := numer(simplify(`conic_eval/RP`(q)(`disc_unstereo/RP`([u,v]))));
 implicitplot(qq,u=-1.1..1.1,v=-1.1..1.1,args[2..-1]);
end:

######################################################################

`is_element/RP_arcs` := proc(xxc)
 if not(type(xxc,[[numeric$3]$3])) then
  return false;
 fi;

 if Determinant(Matrix(xxc)) = 0 then return false; fi;

 return true;
end:

`random_element/RP_arcs` := proc()
 local xxc;
 xxc := [[0$3]$3];

 while Determinant(Matrix(xxc)) = 0 do
  xxc := [seq([seq(rand(-10..10)(),i=1..3)],j=1..3)];
 od;

 return xxc;
end:

`ratio/RP_arcs` := proc(xxc1,xxc2)
 local u,v,w;
 
 u := [seq(dp3(xxc1[i],xxc2[i]),i=1..3)];
 v := [seq(dp3(xxc1[i],xxc1[i]),i=1..3)];
 w := [seq(dp3(xxc2[i],xxc2[i]),i=1..3)];

 if (u *~ u = v *~ w) then
  return u /~ w;
 else
  return NULL;
 fi;
end:

`is_equal/RP_arcs` := proc(xxc1,xxc2)
 local r;
 r := `ratio/RP_arcs`(xxc1,xxc2);

 if r = NULL then return false; fi;
 if r[1] <> r[2] or r[2] <> r[3] then
  return false;
 fi;

 return true;
end:

`is_similar/RP_arcs` := proc(xxc1,xxc2)
 local r;
 r := `ratio/RP_arcs`(xxc1,xxc2);

 if r = NULL then return false; fi;
 if r[1]*r[2] - r[3]^2 <> 0 then
  return false;
 fi;

 return true; 
end:

`is_leq/RP_arcs` := NULL:
`list_elements/RP_arcs` := NULL:
`count_elements/RP_arcs` := NULL:

`arc_eval/RP` := (xxc) -> (t) ->
 (1-t)^2 *~ xxc[1] +~ t^2 *~ xxc[2] +~ (t*(1-t)) *~ xxc[3];

`conic_arc_eval/RP` := (q,xxc) -> (t) ->
 `conic_eval/RP`(q)(`arc_eval/RP`(xxc)(t));

`conic_contains_point/RP` := proc(q,x)
 local err;
 err := abs(`conic_eval/RP`(q)(x));
 return evalb(err = 0);
end:

`conic_contains_arc/RP` := proc(q,xxc)
 local t,err;
 err := max(map(abs,[coeffs(expand(`conic_arc_eval/RP`(q,xxc)(t)),t)]));
 return evalb(err = 0);
end:

`normalise_similar/RP_arcs` := proc(xxc)
 local x,c,n;
 x[1] := xxc[1];
 x[2] := xxc[2];
 c := xxc[3];
 n[1] := nm3(x[1]);
 n[2] := nm3(x[2]);
 return [x[1]/~n[1],x[2]/~n[2],c/~sqrt(n[1]*n[2])];
end:

`arc_coeffs/RP` := proc(st,t)
 local su,u;
 su := factor((1+u)^2 *~ subs(t=u/(1+u),st));
 [map(coeff,su,u,0),
  map(coeff,su,u,2),
  map(coeff,su,u,1)];
end:

`arc_from_tangents/RP` := proc(x1,x2,u1,u2)
 local m1,m2,n,c;
 m1 := Determinant(Matrix([x1,x2,u2]));
 m2 := Determinant(Matrix([x1,x2,u1]));
 n := - Determinant(Matrix([x1,u1,u2])) * m2/m1;
 c := n *~ x2 +~ m2 *~ u2;
 return [m1 *~ x1,m2 *~ x2,n *~ c];
end:

`arc_inv/RP` := (xxc) -> proc(y)
 local u1,u2,u3;
 u1 := Determinant(Matrix(x1,x2,y));
 u2 := Determinant(Matrix(x2,c ,y));
 u3 := Determinant(Matrix(c ,x1,y));
 return u2/(u1+u2); # or u1/(u1+u3);
end:

`conic_from_arc/RP` := proc(xxc)
 local x1,x2,c,M;
 x1,x2,c := op(xxc);
 
 M := Matrix(
  [[x1[1]^2, x1[2]^2, x1[3]^2,
     x1[2]*x1[3], x1[1]*x1[3], x1[1]*x1[2]],
   [x2[1]^2, x2[2]^2, x2[3]^2,
     x2[2]*x2[3], x2[1]*x2[3], x2[1]*x2[2]],
   [2*c[1]*x1[1], 2*c[2]*x1[2], 2*c[3]*x1[3], c[2]*x1[3]+c[3]*x1[2],
     c[1]*x1[3]+c[3]*x1[1], c[1]*x1[2]+c[2]*x1[1]],
   [2*c[1]*x2[1], 2*c[2]*x2[2], 2*c[3]*x2[3], c[2]*x2[3]+c[3]*x2[2],
     c[1]*x2[3]+c[3]*x2[1], c[1]*x2[2]+c[2]*x2[1]],
   [c[1]^2+2*x1[1]*x2[1], c[2]^2+2*x1[2]*x2[2], c[3]^2+2*x1[3]*x2[3],
     c[2]*c[3]+x1[2]*x2[3]+x1[3]*x2[2],
      c[1]*c[3]+x1[1]*x2[3]+x1[3]*x2[1],
       c[1]*c[2]+x1[1]*x2[2]+x1[2]*x2[1]]]
 );
 return NullSpace(M)[1];
end:

`arc_from_rational_conic/RP` := proc(q)
 local x,y,z,f,sol,u0,u1,u2,u,t,Z;
 if not(type(q,[rational$6])) then
  return NULL;
 fi;

 f := `conic_eval/RP`(q)([x,y,z]);
 sol := isolve(f);
 if sol = NULL then return NULL; fi;

 u0 := subs(sol,[x,y,z]);
 u1 := eval(subs(igcd = (() -> 1),u0));
 u2 := u1;
 for Z in indets(u1) do
  if degree(u1[1],Z) = 1 then u2 := subs(Z = 1,u2); fi;
 od:
 u := subs({indets(u2)[1] = t,indets(u2)[2] = 1-t},u2);
 return `arc_coeffs/RP`(u,t);
end:

`arc_from_conic_eigenvalues/RP` := proc(q)
 local Q,E,V,i,v,xxc;
 Q := evalf(Matrix(`conic_matrix/RP`(q),shape=symmetric));
 E,V := Eigenvectors(Q);
 for i from 1 to 3 do 
  v[i] := convert(Column(V,i)/sqrt(abs(E[i])),list); 
 od;
 xxc := [(v[1] +~ v[2])/~2,(v[1] -~ v[2])/~2,v[3]];
 return xxc;
end:

`cut_arc/RP` := proc(xxc,t1,t2)
 local y1,y2,d;
 y1 := `arc_eval/RP`(xxc)(t1);
 y2 := `arc_eval/RP`(xxc)(t2);
 d := (2*(1-t1)*(1-t2)) *~ xxc[1] +~
      (2*t1*t2) *~ xxc[2] +~
      (t1 + t2 - 2*t1*t2) *~ xxc[3];
 return [y1,y2,d];
end:

`shift_arc/RP` := proc(xxc,u)
 [exp(u),exp(-u),1] *~ xxc;
end:

`bulge_arc/RP` := proc(xxc,u)
 local x1,x2,c;
 x1,x2,c := op(xxc);
 if u >= 0 then
  return [x1,x2,u*~c];
 else
  return [x1,x2,u*~c];
 fi;
end:

`disc_plot/arc` := proc(xxc)
 local u,v,tt,m,i,P,e,t0,t1;
 u := `arc_eval/RP`(xxc)(t);
 tt := sort(evalf([op({0,1,fsolve(u[3],t=0..1)})]));
 m := nops(tt);
 P := NULL;
 e := 10.^(-4);
 for i from 1 to m-1 do
  t0 := (1-e) *~ tt[i] +~ e *~ tt[i+1];
  t1 := e *~ tt[i] +~ (1-e) *~ tt[i+1];
  v := simplify(`disc_stereo/RP`(u)) assuming t > t0 and t < t1;
  P := P,plot([op(v),t=t0..t1],args[2..-1]);
 od:
 display(P);
end:

`disc_point_plot/arc` := proc(xxc)
 local i,N,P,u,v,p;
 N := 12;
 P := NULL;
 for i from 0 to N do
  u := evalf(`arc_eval/RP`(xxc)(i/N));
  v := `disc_stereo/RP`(u);
  p := point(v,args[2..-1]);
  P := P,p;
 od:
 display(P);
end:
