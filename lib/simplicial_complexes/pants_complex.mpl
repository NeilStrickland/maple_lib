# The goal here is to set up a simplicial complex K and an embedding of
# |K| in R^3 such that the image is a version of the standard "pair of
# pants space", or in other words a sphere with three discs removed.
# More specifically, we start with the unit sphere in R^3, and remove
# three discs of radius 1/2 centred at points equally spaced around
# the plane perpendicular to [1,1,1].  This has an evident linear action
# of the group G = S_3 x C_2, and everything will be equivariant with
# respect to this.  There is a fundamental domain for the action on S^2
# that is a spherical triangle with one vertex at [1,1,1]/sqrt(3) and
# the other two vertices separated by Pi/3 on the equator perpendicular
# to [1,1,1].  One boundary circle meets this domain in a quarter
# circle, and the other boundary circles do not intersect it at all.
# We start by setting up a triangulation of the fundamental domain
# such that this quarter circle is essentially a subcomplex.  We
# can then propagate this equivariantly and remove the boundary
# discs to obtain a triangulated surface of the required homeomorphism
# type.  We can glue a standard horizontal cylinder to each boundary
# circle to connect to other pieces and so construct various surfaces.
# However, this is ugly because the tangent spaces do not line up
# along the glued circles.  To fix this, we construct a map
# f : S^2 -> R^3 with the property the f is the identity on our
# boundary circles but acts near those circles in such a way as to
# line up the tangent spaces with a horizontal cylinder.

lib_read("brent.mpl"):

make_pants_complex := proc(verbose := false)
 local plot_opts,dp,G,T,U,V,xx,i,j,k,lm,m,v,g,gi,gx,E,R,f2,sphere_retract,
  xa,xb,xc,ua,rb,rels,F,a,n,s,t,u;
 global pants_group,pants_sphere_sector_complex,pants_sphere_complex,
  pants_complex,condensed_pants_complex;
 
 plot_opts := scaling=constrained, axes=none:
 dp := `dot/R`(3);

 if verbose then printf("Making group\n"); fi;
 
 # This is the group S_3 x C_2, which will act isometrically on everything.
 G := table():
 pants_group := eval(G);
 G["elements"] := [seq(seq([op(u),s],u in combinat[permute](3)),s in [1,-1])]:
 G["id"] := [1,2,3,1]:
 G["o"] := (u,v) -> [u[v[1]],u[v[2]],u[v[3]],u[4] * v[4]]:
 G["inv"] := proc(u)
  local ui,i;
  ui := table():
  for i from 1 to 3 do ui[u[i]] := i; od:
  return [ui[1],ui[2],ui[3],u[4]];
 end:

 if verbose then printf("Making skeleton\n"); fi;
 T := table():
 pants_sphere_sector_complex := eval(T):
 
 T["u"] := table([
   1 = [ 2,-1,-1] /~ sqrt(6),
   2 = [ 1, 1,-2] /~ sqrt(6),
   3 = [-1, 2,-1] /~ sqrt(6),
   4 = [-2, 1, 1] /~ sqrt(6),
   5 = [-1,-1, 2] /~ sqrt(6),
   6 = [ 1,-2, 1] /~ sqrt(6),
 ##
   7 = [ 1, 1, 1] /~ sqrt(3),
   8 = [-1,-1,-1] /~ sqrt(3),
 ##
   9 = [ 0, 1,-1] /~ sqrt(2),
  10 = [-1, 1, 0] /~ sqrt(2),
  11 = [-1, 0, 1] /~ sqrt(2),
  12 = [ 0,-1, 1] /~ sqrt(2),
  13 = [ 1,-1, 0] /~ sqrt(2),
  14 = [ 1, 0,-1] /~ sqrt(2)
 ]):

 T["u_index"] := table():
 for i from 0 to 13 do 
  T["u_index"][T["u"][i]] := i;
  T["u_index"][simplify(T["u"][i])] := i;
 od:

 xx := [x[1],x[2],x[3]];
 
 T["act_R3"] := table():
 for g in G["elements"] do 
  gi := G["inv"](g);
  gx := [x[gi[1]],x[gi[2]],x[gi[3]]];
  if g[4] = -1 then 
   gx := expand(gx -~ (2/3 * dp([1,1,1],gx)) *~ [1,1,1]); 
  fi;
  T["act_R3"][g] := unapply(gx,x);
 od:

 T["act_u_table"] := table():
 T["act_u"] := table():
 for g in G["elements"] do 
  T["act_u_table"][g] := 
   table([seq(i = T["u_index"][simplify(T["act_R3"][g](T["u"][i]))],i=0..13)]);
  T["act_u"][g] := (i) -> T["act_u_table"][g][i];
 od:

 T["equator"] := unapply(cos(t) *~ T["u"][1] +~ sin(t) *~ T["u"][9],t):
 T["equator_plot"] := 
  spacecurve(T["equator"](t),t=0..2*Pi,colour=green,plot_opts):
 T["equator_sector_plot"] := 
  spacecurve(T["equator"](t),t=0..Pi/3,colour=green,plot_opts):

 T["longitude"] := table():
 T["longitude_plot"] := table():
 for i from 1 to 6 do 
  T["longitude"][i] :=
   unapply(expand(sin(t) *~ T["u"][7] +~ cos(t) *~ T["u"][i]),t); 
  T["longitude_plot"][i] :=
   spacecurve(T["longitude"][i](t),t=-Pi/2..Pi/2,colour=blue,plot_opts):
 od:
 T["longitude_sector_plot"] := 
  display(
   spacecurve(T["longitude"][1](t),t=0..Pi/2,colour=blue,plot_opts),
   spacecurve(T["longitude"][2](t),t=0..Pi/2,colour=blue,plot_opts),
   plot_opts
  ):

 T["boundary_circle"] := table():
 T["boundary_circle_plot"] := table():
 for i from 1 to 3 do 
  T["boundary_circle"][i] :=
   unapply(expand((sqrt(3)/2) *~ T["u"][2*i-1] +~ (cos(t)/2) *~ T["u"][2*i+7] +~ (sin(t)/2) *~ T["u"][7]),t); 
  T["boundary_circle_plot"][i] :=
   spacecurve(T["boundary_circle"][i](t),t=0..2*Pi,colour=red,plot_opts)
 od:
 T["boundary_circle_sector_plot"] :=
   spacecurve(T["boundary_circle"][1](t),t=0..Pi/2,colour=red,plot_opts):

 T["wire_sphere_plot"]  := sphere(colour=grey,style=wireframe):
 T["solid_sphere_plot"] := sphere(colour=grey,style=patchnogrid):
 T["wire_sector_plot"]  := 
  plot3d(cos(t) *~ T["u"][7] +~ sin(t) *~ (cos(u) *~ T["u"][1] +~ sin(u) *~ T["u"][9]),
	 t = 0 .. Pi/2,u = 0 .. Pi/3,
	 colour=grey,style=wireframe,scaling=constrained, axes=none):
 T["solid_sector_plot"]  := 
  plot3d(cos(t) *~ T["u"][7] +~ sin(t) *~ (cos(u) *~ T["u"][1] +~ sin(u) *~ T["u"][9]),
	 t = 0 .. Pi/2,u = 0 .. Pi/3,
	 colour=grey,style=patchnogrid,scaling=constrained, axes=none):

 T["line_plot"] := display(
  T["equator_plot"],
  seq(T["longitude_plot"][i],i=1..6),
  seq(T["boundary_circle_plot"][i],i=1..3)
 ):
 
 T["sphere_plot"] := display(
  T["solid_sphere_plot"],T["line_plot"],
  plot_opts
 ):

 T["line_sector_plot"] := display(
  T["equator_sector_plot"],
  T["longitude_sector_plot"],
  T["boundary_circle_sector_plot"],
  plot_opts
 ):

 T["sector_plot"] := display(
  T["solid_sector_plot"],T["line_sector_plot"],
  plot_opts
 ):

 lm := 4:
 m := 2 ^ lm:
 T["m"] := m:

 if verbose then printf("Making simplices\n"); fi;

 v := (i,j) -> [i/m,j/m,(m-i-j)/m]:

 T["vertices"] := [seq(seq(v(i,j),j=0..m - i),i=0..m)]:

 T["edges"] := [
  seq(seq([v(i,j),v(i+1,j)],j=0..m-1-i),i=0..m-1),
  seq(seq([v(i,j),v(i,j+1)],j=0..m-1-i),i=0..m-1),
  seq(seq([v(i+1,j),v(i,j+1)],j=0..m-1-i),i=0..m-1),
 NULL
 ]:

 T["faces"] := [
  seq(seq([v(i,j),v(i+1,j),v(i,j+1)],j=0..m-1-i),i=0..m-1),
  seq(seq([v(i,j+1),v(i+1,j),v(i+1,j+1)],j=0..m-2-i),i=0..m-2)
 ]:

 T["max_simplices"] := T["faces"]:

 if verbose then printf("Making explicit embedding\n"); fi;

 unassign('i');
 T["f0"] := unapply(i[1] *~ T["u"][1] +~ i[2] *~ T["u"][2] +~ i[3] *~ T["u"][7],i):
 T["f1"] := proc(i) local x; x := T["f0"](i); return x /~ sqrt(add(x[j]^2,j=1..3)); end:
 T["embedding0"] := table():
 T["embedding1"] := table():
 for i in T["vertices"] do 
  T["embedding0"][i] := T["f0"](i);
  T["embedding1"][i] := T["f1"](i);
 od:

 E := table():
 for i in T["vertices"] do E[i] := NULL; od:

 for i from 0 to m do 
   E[[m-i,i,0] /~ m] := T["equator"](i/m * Pi/3);
   E[[0,m-i,i] /~ m] := T["longitude"][2](i/m * Pi/2);
 od:
 for i from 0 to m/2 do 
   E[[m-i,0,i]       /~ m] := T["longitude"][1]((2*i/m) * Pi/6); 
   E[[m/2-i,0,m/2+i] /~ m] := T["longitude"][1]((1+4*i/m) * Pi/6); 
   E[[m/2,m/2-i,i]   /~ m] := T["boundary_circle"][1]((2*i/m) * Pi/2);
 od:

 sphere_retract := (u) -> evalf(u /~ sqrt(add(u[i]^2,i=1..3))):

 `midpoint_extend/simplicial_complex`(E,4,sphere_retract):
 T["embedding2"] := eval(E):
 T["embedding"] := eval(E):
 `plot/simplicial_complex`(T):
 `surface_plot/simplicial_complex`(T):

 T["proj"] := table():
 for k from 1 to 3 do 
  T["proj"][k] := unapply(expand(xx - dp(x,T["u"][2*k-1]) *~ T["u"][2*k-1]),x);
 od:

 T["proj_a"] := unapply([dp(xx,T["u"][ 1]),dp(xx,T["u"][12])],x):
 T["proj_b"] := unapply([dp(xx,T["u"][ 5]),dp(xx,T["u"][ 7])],x):
 T["proj_c"] := unapply([dp(xx,T["u"][ 1]),dp(xx,T["u"][ 7])],x):
 T["proj_d"] := unapply([dp(xx,T["u"][12]),dp(xx,T["u"][ 7])],x):

 unassign('s');
 
 T["unproj_a"] := unapply(s[1] *~ T["u"][ 1] +~ s[2] *~ T["u"][12], s); 
 T["unproj_b"] := unapply(s[1] *~ T["u"][ 5] +~ s[2] *~ T["u"][ 7], s); 
 T["unproj_c"] := unapply(s[1] *~ T["u"][ 1] +~ s[2] *~ T["u"][ 7], s); 
 T["unproj_d"] := unapply(s[1] *~ T["u"][12] +~ s[2] *~ T["u"][ 7] +~ (sqrt(3)/2) *~ T["u"][1], s); 

 T["g"] := unapply(expand(mul(dp(x,T["u"][2*j-1]) - sqrt(3)/2,j=1..3)),x):
 T["h"] := unapply(expand((2 + dp(x,T["u"][7]) ^ 2)*sqrt(3)/4),x):

 # Here we define a particular polynomial function k(x), and then we
 # define f(x) in terms of k(x).  Most of the desired properties hold
 # independently of the choice of k(x).  Our particular choice is
 # designed to straighten out the tangent spaces on the boundary
 # circles and ensure that the width of he surface in the centre
 # is the same as the width of the circles.
 T["k"] := (x) -> (20 + 5 * sqrt(2) * x[1] - 15 * x[1]^2 + 5 * sqrt(2) * x[1]^3 + 
		   (4 * x[1] - 3 * sqrt(2)) * (x[2] + x[3]) + 
		   (8 * sqrt(2) * x[1] - 26) * x[2] * x[3] + 
		   (-5) * sqrt(2) * (x[2] + x[3]) * x[2] * x[3])/27:
 T["f2"] := unapply(simplify(
   xx +~ 
    (T["g"](x)/T["h"](x)) *~ (
      T["k"]([x[1],x[2],x[3]]) *~ T["proj"][1](x) +~
      T["k"]([x[2],x[3],x[1]]) *~ T["proj"][2](x) +~
      T["k"]([x[3],x[1],x[2]]) *~ T["proj"][3](x))),
   x):

 for i in T["vertices"] do 
  T["embedding3"][i] := evalf(T["f2"](T["embedding2"][i]));
 od:
 T["embedding"] := eval(T["embedding4"]);

 if verbose then printf("Making implicit embedding\n"); fi;

 # We now start to define an alternative embedding, using the surface
 # where the following function is zero.
 T["l"] := unapply(
  12*sqrt(3)*T["g"](xx) + (1-dp(xx,xx))*(27+6*(x[1]*x[2]+x[2]*x[3]+x[3]*x[1])+
  8*sqrt(3)*T["g"](xx)-6*dp(xx,xx)),x):
 T["l_min_root"] := fsolve(expand(T["l"]((-t) *~ T["u"][1])),t=0.68..0.70);
 T["l_max_root"] := fsolve(expand(T["l"](t *~ T["u"][1])),t=1.42..1.43);
 xa := (r * cos(t)) *~ T["u"][1] +~ (r * sin(t)) *~ T["u"][9] +~ u *~ T["u"][7]:
 ua := solve(simplify(expand(T["l"](xa))),u)[1]:
 ua := sqrt(factor(ua^2)):
 xa := subs(u = ua,xa):
 T["chart_a"] := unapply(xa,r,t):
 xb := (r * cos(t)) *~ T["u"][9] +~ (r * sin(t)) *~ T["u"][7] +~ u *~ T["u"][1]:
 rb := solve(simplify(expand(T["l"](xb))),r)[3]:
 rb := 1/sqrt(factor(expand(rationalize(1/rb^2)))):
 xb := subs(r = rb,xb): 
 T["chart_b"] := unapply(xb,u,t):
 xc := (a[0] - a[1] * r^2 - a[2] * r^4) *~ T["u"][1] +~ r *~ (cos(t) *~ T["u"][9] +~ sin(t) *~ T["u"][7]):
 rels := expand([coeffs(collect(simplify(expand(convert(series(T["l"](xc),r=0,5),polynom,r))),r),r)]):
 xc := expand(evalf(subs(a[0] = T["l_max_root"],subs(solve([rels[2],rels[3]],{a[1],a[2]}),xc)))):
 T["chart_c"] := unapply(xc,r,t):

 T["dl"] := unapply([seq(diff(T["l"](xx),x[i]),i=1..3)],x);
 
 T["retract"] := proc(x)
  local g,y,sols;
  g := evalf(T["dl"](x));
  g := g /~ sqrt(add(g[i]^2,i=1..3));
  y := x +~ t *~ g;
  sols := [fsolve(evalf(expand(T["l"](y))),t)];
  sols := select(t -> abs(t) = min(map(abs,sols)),sols);
  if sols = [] then error("No solutions"); fi;
  return(evalf(subs(t = sols[1],y)));
 end:

 T["step"] := proc(q,d0,proj,unproj)
  local xx,st0,mx,dx,g,h,sol;
  xx  := eval(unproj([s,t]));
  st0 := eval(proj(q));
  mx := evalf(T["l"](xx));
  dx := (s - st0[1])^2 + (t - st0[2])^2 - d0^2;
  g := evalf(subs({s = st0[1],t = st0[2]},[-diff(mx,t),diff(mx,s)]));
  g := (d0 / sqrt(g[1]^2+g[2]^2)) *~ g;
  h := st0 +~ g;
  sol := fsolve({mx,dx},{s = h[1], t = h[2]});
  return evalf(subs(sol,xx));
 end:

 F[0] := (E) -> proc(d0)
  local i;
  E[[1,0,0]] := evalf(T["l_max_root"] *~ T["u"][1]);
  for i from 1 to 8 do
   E[[16-i,i,0] /~ 16] := T["step"](E[[17-i,i-1,0]/~16],d0,T["proj_a"],T["unproj_a"]):
  od:
  return table(["err" = evalf(sqrt(3)/2 - dp(T["u"][1],E[[1/2,1/2,0]]))]);
 end:

 F[1] := (E) -> proc(d0)
  global p; local i;
  E[[1/2,1/2,0]] := T["u"][14];
  for i from 1 to 8 do
   E[[8-i,8+i,0]/~16] := T["step"](E[[9-i,7+i,0]/~16],d0,T["proj_a"],T["unproj_a"]):
  od:
  return table(["err" = evalf(dp(T["u"][10],E[[0,1,0]]))]);
 end:

 F[2] := (E) -> proc(d0)
  global p; local i;
  E[[0,1,0]] := evalf(T["l_min_root"] *~ T["u"][2]):
  for i from 1 to 16 do
   E[[0,16-i,i]/~16] := T["step"](E[[0,17-i,i-1]/~16],d0,T["proj_b"],T["unproj_b"]):
  od:
  return table(["err" = evalf(-dp(T["u"][9],E[[0,0,1]]))]);
 end:

 F[3] := (E) -> proc(d0)
  global p; local i;
  E[[0,0,1]] := T["u"][7] /~ 2:
  for i from 1 to 8 do
   E[[i,0,16-i]/~16] := T["step"](E[[i-1,0,17-i]/~16],d0,T["proj_c"],T["unproj_c"]):
  od:
  return table(["err" = evalf(dp(E[[1/2,0,1/2]],T["u"][1]) - sqrt(3)/2)]);
 end:

 F[4] := (E) -> proc(d0)
  global p; local i,e;
  E[[1/2,0,1/2]] := (sqrt(3)/2) *~ T["u"][1] +~ (1/2) *~ T["u"][7];
  for i from 1 to 8 do
   E[[8+i,0,8-i]/~16] := T["step"](E[[7+i,0,9-i]/~16],d0,T["proj_c"],T["unproj_c"]):
  od:
  e := - evalf(dp(E[[1,0,0]],T["u"][7]));
  E[[1,0,0]] := evalf(T["l_max_root"] *~ T["u"][1]);
  return table(["err" = e]);
 end:

 F[5] := (E) -> proc(d0)
  global p; local i,e;
  for i from 1 to 8 do 
   E[[8,8-i,i]/~16] := T["step"](E[[8,9-i,i-1]/~16],d0,T["proj_d"],T["unproj_d"]): 
  od: 
  e := - evalf(dp(E[[1/2,0,1/2]],T["u"][9]));
  E[[1/2,0,1/2]] := (sqrt(3)/2) *~ T["u"][1] +~ (1/2) *~ T["u"][7];
  return table(["err" = e]);
 end:

 E := table():
 for i in T["vertices"] do E[i] := NULL; od:
 T["F_step"] := table([0 = 0.10, 1 = 0.06, 2 = 0.05, 3 = 0.10, 4 = 0.10, 5 = 0.09]):
 T["F_error"] := table():
 for i from 0 to 5 do
  T["F_step"][i] :=
   brent_fsolve(F[i](E),T["F_step"][i],T["F_step"][i] + 0.01,false,false,10.^(-10))[1];
  T["F_error"][i] := F[i](E)(T["F_step"][i]);
 od:

 `midpoint_extend/simplicial_complex`(E,4,T["retract"]):

 T["embedding4"] := eval(E);
 
 if verbose then printf("Extending equivariantly\n"); fi;

 U := table():
 pants_sphere_complex := eval(U);
 U["act_i"] := table():
 U["act_i"][[1,2,3, 1]] := (j) -> [ j[1], j[2], j[3], j[4]]:
 U["act_i"][[2,3,1, 1]] := (j) -> [-j[2],-j[3], j[1], j[4]]:
 U["act_i"][[3,1,2, 1]] := (j) -> [ j[3],-j[1],-j[2], j[4]]:
 U["act_i"][[2,1,3, 1]] := (j) -> [ j[3], j[2], j[1], j[4]]:
 U["act_i"][[3,2,1, 1]] := (j) -> [-j[2],-j[1], j[3], j[4]]:
 U["act_i"][[1,3,2, 1]] := (j) -> [ j[1],-j[3],-j[2], j[4]]:
 U["act_i"][[1,2,3,-1]] := (j) -> [ j[1], j[2], j[3],-j[4]]:
 U["act_i"][[2,3,1,-1]] := (j) -> [-j[2],-j[3], j[1],-j[4]]:
 U["act_i"][[3,1,2,-1]] := (j) -> [ j[3],-j[1],-j[2],-j[4]]:
 U["act_i"][[2,1,3,-1]] := (j) -> [ j[3], j[2], j[1],-j[4]]:
 U["act_i"][[3,2,1,-1]] := (j) -> [-j[2],-j[1], j[3],-j[4]]:
 U["act_i"][[1,3,2,-1]] := (j) -> [ j[1],-j[3],-j[2],-j[4]]:

 U["vertex_convert"] := (i) -> [i[1],i[2],0,i[3]]:
 U["edge_convert"]   := (e) -> sort(map(U["vertex_convert"],e)):
 U["face_convert"]   := (f) -> sort(map(U["vertex_convert"],f)):

 U["embedding0"] := table():
 U["embedding1"] := table():
 U["embedding2"] := table():
 U["embedding3"] := table():
 U["embedding4"] := table():
 U["vertices"] := map(U["vertex_convert"],T["vertices"]):
 for i in T["vertices"] do 
  U["embedding0"][U["vertex_convert"](i)] := evalf(T["embedding0"][i]);
  U["embedding1"][U["vertex_convert"](i)] := evalf(T["embedding1"][i]);
  U["embedding2"][U["vertex_convert"](i)] := evalf(T["embedding2"][i]);
  U["embedding3"][U["vertex_convert"](i)] := evalf(T["embedding3"][i]);
  U["embedding4"][U["vertex_convert"](i)] := evalf(T["embedding4"][i]);
 od:

 for i in U["vertices"] do
  for g in G["elements"] do 
   U["embedding0"][U["act_i"][g](i)] := evalf(T["act_R3"][g](U["embedding0"][i]));
   U["embedding1"][U["act_i"][g](i)] := evalf(T["act_R3"][g](U["embedding1"][i]));
   U["embedding2"][U["act_i"][g](i)] := evalf(T["act_R3"][g](U["embedding2"][i]));
   U["embedding3"][U["act_i"][g](i)] := evalf(T["act_R3"][g](U["embedding3"][i]));
   U["embedding4"][U["act_i"][g](i)] := evalf(T["act_R3"][g](U["embedding4"][i]));
  od:
 od:
 U["embedding"] := eval(U["embedding4"]);

 U["vertices"] := sort(map(op,[indices(U["embedding0"])])):
 U["edges"] :=
  {seq(seq(sort(map(U["act_i"][g],U["edge_convert"](e))),
    e in T["edges"]),g in G["elements"])}:
 U["edges"] := sort([op(U["edges"])]):
 U["faces"] :=
  {seq(seq(sort(map(U["act_i"][g],U["face_convert"](f))),
    f in T["faces"]),g in G["elements"])}:
 U["faces"] := sort([op(U["faces"])]):

 R := T["act_R3"][[1,2,3,-1]];
 f2 := T["f2"];
 
 U["smooth_plot"] := 
  display(
   plot3d(  f2(sqrt(1-r^2) *~ T["u"][7] +~ (r * cos(t)) *~ T["u"][1] +~ (r * sin(t)) *~ T["u"][9]),
          r=0..0.6,t=0..2*Pi,style=patchnogrid),
   plot3d(R(f2(sqrt(1-r^2) *~ T["u"][7] +~ (r * cos(t)) *~ T["u"][1] +~ (r * sin(t)) *~ T["u"][9])),
          r=0..0.6,t=0..2*Pi,style=patchnogrid),
   plot3d(  f2(cos(s) *~ T["u"][7] +~ (sin(s) * cos(t)) *~ T["u"][1] +~ (sin(s) * sin(t)) *~ T["u"][9]),
          s=0.2*Pi..0.8*Pi,t=0..2*Pi,style=patchnogrid,numpoints=4000),
   plot_opts
  );

 U["chart_plot"] := display(
  plot3d(xa,r=0..0.5,t=0..2*Pi,style=patchnogrid),
  plot3d(T["act_R3"][[1,2,3,-1]](xa),r=0..0.5,t=0..2*Pi,style=patchnogrid),
  plot3d(xb,u=0..1.4,t=0..2*Pi,style=patchnogrid),
  plot3d(T["act_R3"][[2,3,1,1]](xb),u=0..1.4,t=0..2*Pi,style=patchnogrid),
  plot3d(T["act_R3"][[3,1,2,1]](xb),u=0..1.4,t=0..2*Pi,style=patchnogrid),
  plot3d(xc,r=0..0.3,t=0..2*Pi,style=patchnogrid),
  plot3d(T["act_R3"][[2,3,1,1]](xc),r=0..0.3,t=0..2*Pi,style=patchnogrid),
  plot3d(T["act_R3"][[3,1,2,1]](xc),r=0..0.3,t=0..2*Pi,style=patchnogrid),
  scaling=constrained,axes=none):

 if verbose then printf("Trimming\n"); fi;

 V := table():
 pants_complex := eval(V);
 V["vertices"] := select(i -> max(i[1],-i[2],i[3]) <= 1/2,U["vertices"]):
 V["edges"] := select(e -> {op(e)} minus {op(V["vertices"])} = {}, U["edges"]):
 V["faces"] := select(f -> {op(f)} minus {op(V["vertices"])} = {}, U["faces"]):
 V["max_simplices"] := V["faces"]:
 V["embedding0"] := table():
 V["embedding1"] := table():
 V["embedding2"] := table():
 V["embedding3"] := table():
 V["embedding4"] := table():
 for i in V["vertices"] do
  V["embedding0"][i] := U["embedding0"][i];
  V["embedding1"][i] := U["embedding1"][i];
  V["embedding2"][i] := U["embedding2"][i];
  V["embedding3"][i] := U["embedding3"][i];
  V["embedding4"][i] := U["embedding4"][i];
 od:
 V["embedding"] := V["embedding4"]:

 V["normal"] := table():
 for i in V["vertices"] do
  n := evalf(T["dl"](V["embedding"][i]));
  n := n /~ dp(n,n);
  V["normal"][i] := n;
 od:
 
 V["chart_plot"] :=
  display(
   plot3d(xa,r=0..0.5,t=0..2*Pi,style=patchnogrid),
   plot3d(T["act_R3"][[1,2,3,-1]](xa),r=0..0.5,t=0..2*Pi,style=patchnogrid),
   plot3d(xb,u=0..sqrt(3.)/2,t=0..2*Pi,style=patchnogrid),
   plot3d(T["act_R3"][[2,3,1,1]](xb),u=0..sqrt(3.)/2,t=0..2*Pi,style=patchnogrid),
   plot3d(T["act_R3"][[3,1,2,1]](xb),u=0..sqrt(3.)/2,t=0..2*Pi,style=patchnogrid),
  scaling=constrained,axes=none):

 condensed_pants_complex := 
  `condense/simplicial_complex`(pants_complex);

 if verbose then printf("Generating javascript\n"); fi;
 `set_javascript/simplicial_complex`(condensed_pants_complex);
end:

`base/pants` := table([
 "centre" = [0,0,0],
 "circle_centres" = [[sqrt(3)/2,0,0],[-sqrt(3)/4,3/4,0],[-sqrt(3)/4,-3/4,0]],
 "top" = [0,0,1/2]
]):

`outline/pants` := proc(P)
 local c,z,t;
 c := P["centre"];
 z := 2 *~ (P["top"] -~ P["centre"]);
 display(
  seq(line(P["centre"],u,colour=green),u in P["circle_centres"]),
  seq(spacecurve(u +~ (cos(t)/sqrt(3)) *~ cross_product(u -~ c,z) +~ (sin(t)/2) *~ z,t=0..2*Pi,colour=red),
       u in P["circle_centres"]),
  scaling=constrained,axes=none
 );
end:

`rough_plot/pants` := proc(P)
 local c,z,t,u,v,w,X;
 c := P["centre"];
 z := 2 *~ (P["top"] -~ P["centre"]);
 X := NULL;
 for u in P["circle_centres"] do 
  v := evalf((u -~ c) *~ (2/sqrt(3)));
  w := cross_product(v,z);
  X := X,plot3d(c +~ (s * abs(cos(t))/4 + (1-s) * sqrt(3)/2) *~ v 
                +~ (cos(t)/2) *~ w +~ (sin(t)/2) *~ z,
                s=0..1,t=0..2*Pi,style=patchnogrid,scaling=constrained,axes=none); 
 od:
 return(display(X));
end:

`plot/pants` := proc(P)
 local dp,h,c,b,u,v,w,p,f,X;

 dp := (u,v) -> add(u[i] * v[i],i=1..3);
 h := (x) -> evalf(x /~ sqrt(dp(x,x)));
 c := evalf(P["centre"]);
 b := map(x -> x -~ c,P["circle_centres"]);
 u := h(b[1]);
 v := h(b[2] -~ b[3]);
 w := h(P["top"] -~ c);
 p := pants_sphere_sector_complex["u"];
 f := unapply(c +~ dp(x,p[1]) *~ u +~ dp(x,p[9]) *~ v +~ dp(x,p[7]) *~ w,x);
 X := `map/simplicial_complex`(f,condensed_pants_complex);
 return `surface_plot/simplicial_complex`(X);
end:

`map/pants` := proc(f,P) 
 return table([
  "centre" = f(P["centre"]),
  "circle_centres" = map(f,P["circle_centres"]),
  "top" = f(P["top"])
 ]);
end:

`sprout/pants` := proc(P,i)
 local Q,u,c;
 c := P["centre"];
 u := P["circle_centres"][i] -~ c;
 Q := table():
 Q["centre"] := c +~ 2 *~ u;
 Q["circle_centres"] := map(v -> 2 *~ c + 2 *~ u -~ v,P["circle_centres"]);
 Q["top"] := P["top"] -~ P["centre"] +~ Q["centre"]; 
 return eval(Q);
end:


`pants_tube/base` := table([
  "centre"    = [0,0,0],
  "direction" = [1,0,0],  # unit vector
  "bend"      = [0,1,0],  # unit vector
  "length"    = 1,
  "curvature" = 0
]):

`outline/pants_tube` := proc(T)
 local c,d,b,l,k,w,x,y,z,s,t0,t;
 c := T["centre"];
 d := T["direction"];
 b := T["bend"];
 l := T["length"];
 k := T["curvature"];
 w := cross_product(d,b);
 x := c -~ (`C/pants_tube`(t*l*k/2)*t^2*l^2*k/8) *~ b +~ (`S/pants_tube`(t*l*k/2)*t*l/2) *~ d;
 y := cos(t*l*k/2) *~ b +~ sin(t*l*k/2) *~ d;
 z := x +~ (cos(s)/2) *~ y +~ (sin(s)/2) *~ w;
 return display(
  spacecurve(x,t = -1..1,colour=cyan),
  spacecurve(subs(t=-1,z),s=0..2*Pi,colour=orange),
  spacecurve(subs(t= 1,z),s=0..2*Pi,colour=orange),
  scaling=constrained,axes=none
 );
end:

`S/pants_tube` := unapply(convert(series(sin(x)/x,x=0,11),polynom,x),x);
`C/pants_tube` := unapply(convert(series(2*(1-cos(x))/x^2,x=0,11),polynom,x),x);
`A/pants_tube` := unapply(convert(series(arcsin(x)/x,x=0,11),polynom,x),x);

`plot/pants_tube` := proc(T)
 local c,d,b,l,k,w,x,y,z,s,t;
 c := T["centre"];
 d := T["direction"];
 b := T["bend"];
 l := T["length"];
 k := T["curvature"];
 w := cross_product(d,b);
 x := c -~ (`C/pants_tube`(t*l*k/2)*t^2*l^2*k/8) *~ b +~ (`S/pants_tube`(t*l*k/2)*t*l/2) *~ d;
 y := cos(t*l*k/2) *~ b +~ sin(t*l*k/2) *~ d;
 z := x +~ (cos(s)/2) *~ y +~ (sin(s)/2) *~ w;
 return display(
  plot3d(z,t=-1..1,s=0..2*Pi,style=patchnogrid),
  scaling=constrained,axes=none
 );
end:

`map/pants_tube` := proc(f,T)
 local U;
 U := table():
 U["centre"] := f(T["centre"]);
 U["direction"] := f(T["centre"] +~ T["direction"]) -~ U["centre"];
 U["bend"]      := f(T["centre"] +~ T["bend"]     ) -~ U["centre"];
 U["length"]    := T["length"];
 U["curvature"] := T["curvature"];
 return eval(U);
end:

`joiner/pants_tube` := proc(c1,n1,c2,n2_)
 local dp,d,s,c0,ca,sa,n2,err,p,q,k,l,b,c,T,alpha,m,pic;
 dp := `dot/R`(3);

 d := evalf(c2 -~ c1);
 s := sqrt(dp(d,d));           # straight line length
 d := d /~ s;                  # unit vector c1 -> c2
 c0 := evalf((c1 +~ c2) /~ 2); # straight line midpoint

 ca := -evalf(dp(n1,d));       # cos(alpha/2)
 sa := sqrt(1 - ca * ca);      # sin(alpha/2)

 if nargs >= 4 then 
  n2 := n2_;
 else
  n2 := n1 +~ (2 * p) *~ d;
 fi;

 k := 2 * sa/s;       # curvature
 q := s/2 * sqrt((1-ca)/(1+ca));

 err := evalf(cross_product(d,n2 -~ n1));
 err := sqrt(dp(err,err));
 if err > 10.^(-6) then
  error("Non-matching circles");
 fi;

 b := -~ evalf(n1 +~ n2);

 if sqrt(dp(b,b)) < 10.^(-4) then
  # Tube will be straight.  Set b to be an arbitrary vector
  # orthogonal to d.

  b := [1,0,0]; p := abs(d[1]);
  if abs(d[2]) < p then b := [0,1,0]; p := abs(d[2]); fi;
  if abs(d[3]) < p then b := [0,0,1]; p := abs(d[3]); fi;
  b := b -~ dp(d,b) *~ d;
  b := b /~ sqrt(dp(b,b));
  k := 0;
  c := c0;
  l := s;
 else
  b := b /~ sqrt(dp(b,b));
  c := evalf(c0 +~ q *~ b);
#  l := s * `A/pants_tube`(s * k / 2);
  alpha := 2 * arccos(ca);
  l := alpha / k;
  m := c -~ b /~ k;
  pic := display(
   point(c1,colour=black),
   line(c1,c2,colour=black),
   arrow(c1,0.3*~n1,cross_product(b,d),0.05,0.1,0.025,colour=magenta),
   arrow(c2,0.3*~n2,cross_product(b,d),0.05,0.1,0.025,colour=magenta),
   line(c0,c,colour=orange),
   line(m,c1,colour=purple),
   line(m,c2,colour=purple),
   spacecurve(m +~ (cos(t)/k) *~ b +~ (sin(t)/k) *~ d,t=-alpha/2..alpha/2,colour=cyan),
   scaling=constrained,axes=none
  );
 fi;

 T := table([
  "c1" = evalf(c1), "c2" = evalf(c2), "n1" = evalf(n1), "n2" = evalf(n2), "d" = d, "s" = s, "c0" = c0, "ca" = ca, "sa" = sa, "q" = q, "alpha" = alpha,
  "centre" = c,
  "direction" = d,
  "bend" = b,
  "length" = l,
  "curvature" = k,
  "pic" = pic
 ]);

 return eval(T);
end:

`pants_joiner/pants_tube` := proc(P1,i1,P2,i2)
 local dp,a1,a2,c1,c2,n1,n2;
 dp := `dot/R`(3);
 a1 := P1["centre"];
 a2 := P2["centre"];
 c1 := P1["circle_centres"][modp(i1-1,3)+1];
 c2 := P2["circle_centres"][modp(i2-1,3)+1];
 n1 := a1 -~ c1;
 n2 := a2 -~ c2;
 n1 := n1 /~ sqrt(dp(n1,n1));
 n2 := n2 /~ sqrt(dp(n2,n2));
 return `joiner/pants_tube`(c1,n1,c2,n2);
end:

