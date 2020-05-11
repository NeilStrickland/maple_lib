make_example_surfaces := proc()
 global example_surface;
 local P,T,R,dp,a,u,i,j,k;
 
 dp := (u,v) -> add(u[i] * v[i],i=1..3):
 R := (x) -> [-x[1]/2+sqrt(3)*x[2]/2,-sqrt(3)*x[1]/2-x[2]/2,x[3]]:

 P := table():
 P[0] := `map/pants`(x -> x,`base/pants`):
 for i from 1 to 5 do P[i] := `sprout/pants`(P[i-1],modp(i-1,3)+1); od:
 T := table():
 T[0] := `pants_joiner/pants_tube`(P[0],2,P[1],3):
 T[1] := `pants_joiner/pants_tube`(P[2],1,P[3],2):
 T[2] := `pants_joiner/pants_tube`(P[4],3,P[5],1):
 example_surface[0] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T))
 ):

 P := table():
 T := table():
 P[0] := eval(`base/pants`):
 P[1] := `sprout/pants`(P[0],1):
 T[0] := `pants_joiner/pants_tube`(P[0],2,P[1],3):
 T[1] := `pants_joiner/pants_tube`(P[0],3,P[1],2):
 example_surface[1] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T))
 ):

 P := table(): T := table():
 P[0] := eval(`base/pants`):
 P[1] := `sprout/pants`(P[0],1):
 P[2] := `map/pants`((x) -> x +~ [0,3,0],P[0]):
 P[3] := `map/pants`((x) -> x +~ [0,3,0],P[1]):
 T[0] := `pants_joiner/pants_tube`(P[0],2,P[2],3):
 T[1] := `pants_joiner/pants_tube`(P[1],3,P[3],2):
 T[3] := `pants_joiner/pants_tube`(P[0],3,P[1],2):
 T[4] := `pants_joiner/pants_tube`(P[2],2,P[3],3):
 example_surface[2] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T))
 ):

 P := table(): T := table():
 P[0] := eval(`base/pants`):
 P[1] := `sprout/pants`(P[0],1):
 T[0] := `pants_joiner/pants_tube`(P[0],2,P[0],3):
 T[1] := `pants_joiner/pants_tube`(P[1],2,P[1],3):
 example_surface[3] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T))
 ):

 a := 2:
 u := table():
 P := table():
 T := table():
 u[0] := simplex_embedding([1,0,0,0]):
 u[1] := simplex_embedding([0,1,0,0]):
 u[2] := simplex_embedding([0,0,1,0]):
 u[3] := simplex_embedding([0,0,0,1]):
 for i from 0 to 3 do 
  P[i] := table([
   "centre" = a *~ u[i],
   "circle_centres" = [seq(simplify(a *~ u[i] +~ (u[j] -~ dp(u[j],u[i]) *~ u[i]) *~ (sqrt(27/32))),j in {0,1,2,3} minus {i})],
   "top" = (a + 1/2) *~ u[i]
  ]);
 od:
 T[0,1] := `pants_joiner/pants_tube`(P[0],1,P[1],1):
 T[0,2] := `pants_joiner/pants_tube`(P[0],2,P[2],1):
 T[0,3] := `pants_joiner/pants_tube`(P[0],3,P[3],1):
 T[1,2] := `pants_joiner/pants_tube`(P[1],2,P[2],2):
 T[1,3] := `pants_joiner/pants_tube`(P[1],3,P[3],2):
 T[2,3] := `pants_joiner/pants_tube`(P[2],3,P[3],3):
 example_surface[4] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T)),
  axes=none,scaling=constrained
 ):

 P := table():
 T := table():
 a := 2:
 for i in [-1,1] do 
  for j in [-1,1] do
   for k in [-1,1] do 
    P[i,j,k] := table([
     "centre" = a *~ [i,j,k],
     "circle_centres" = evalf(map(x -> (a *~ [i,j,k] +~ x /~ sqrt(8)), 
			    [[-2*i,j,k],[i,-2*j,k],[i,j,-2*k]])),
     "top" = evalf((a + 1/(2*sqrt(3))) *~ [i,j,k])
    ]);
   od:
  od:
 od:
 T[ 0, 1, 1] := `pants_joiner/pants_tube`(P[ 1, 1, 1],1,P[-1, 1, 1],1):
 T[ 0, 1,-1] := `pants_joiner/pants_tube`(P[ 1, 1,-1],1,P[-1, 1,-1],1):
 T[ 0,-1, 1] := `pants_joiner/pants_tube`(P[ 1,-1, 1],1,P[-1,-1, 1],1):
 T[ 0,-1,-1] := `pants_joiner/pants_tube`(P[ 1,-1,-1],1,P[-1,-1,-1],1):
 T[ 1, 0, 1] := `pants_joiner/pants_tube`(P[ 1, 1, 1],2,P[ 1,-1, 1],2):
 T[ 1, 0,-1] := `pants_joiner/pants_tube`(P[ 1, 1,-1],2,P[ 1,-1,-1],2):
 T[-1, 0, 1] := `pants_joiner/pants_tube`(P[-1, 1, 1],2,P[-1,-1, 1],2):
 T[-1, 0,-1] := `pants_joiner/pants_tube`(P[-1, 1,-1],2,P[-1,-1,-1],2):
 T[ 1, 1, 0] := `pants_joiner/pants_tube`(P[ 1, 1, 1],3,P[ 1, 1,-1],3):
 T[ 1,-1, 0] := `pants_joiner/pants_tube`(P[ 1,-1, 1],3,P[ 1,-1,-1],3):
 T[-1, 1, 0] := `pants_joiner/pants_tube`(P[-1, 1, 1],3,P[-1, 1,-1],3):
 T[-1,-1, 0] := `pants_joiner/pants_tube`(P[-1,-1, 1],3,P[-1,-1,-1],3):
 example_surface[5] := display(
  seq(`rough_plot/pants`(op(X)),X in entries(P)),
  seq(`plot/pants_tube`(op(X)),X in entries(T)),
  axes=none,scaling=constrained
 ):

 return eval(example_surface);
end:
