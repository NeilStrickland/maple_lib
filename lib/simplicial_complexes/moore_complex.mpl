moore_net_complex := proc(n::posint)
 local T,m,i;

 m := 3*n;

 T["vertices"] := {seq(i,i=1..2*m+1)};
 T["faces"] := {
  seq({1,2+i,2+modp(i+1,m)},i=0..m-1),
  seq({2+i,2+modp(i+1,m),m+2+modp(i+1,m)},i=0..m-1),
  seq({2+i,m+2+i,m+2+modp(i+1,m)},i=0..m-1)
 };

 T["max_simplices"] := T["faces"];
 
 T["embedding_dim"] := 2;
 T["embedding"] := table([
  1 = [0,0],
  seq(i = [2*cos(2*Pi*(i-2)/m),2*sin(2*Pi*(i-2)/m)],i=2..m+1),
  seq(i = [3*cos(2*Pi*(i-m-2)/m),3*sin(2*Pi*(i-m-2)/m)],i=m+2..2*m+1)
 ]);

 T["plot"] :=
   `plot/simplicial_complex`(T["vertices"])(T["faces"],2,T["embedding"]);

 return eval(T);
end:

moore_complex := proc(n::posint)
 local T0,T,m,i;

 m := 3*n;

 T["vertices"] := {seq(i,i=1..m+4)};
 T["faces"] := {
  seq({1,2+i,2+modp(i+1,m)},i=0..m-1),
  seq({2+i,2+modp(i+1,m),m+2+modp(i+1,3)},i=0..m-1),
  seq({2+i,m+2+modp(i,3),m+2+modp(i+1,3)},i=0..m-1)
 };
 T["max_simplices"] := T["faces"];

 return eval(T);
end:

punctured_moore_complex := proc(n::posint)
 local T,E,F,m,a,R0,R1,tor,tor_arc,i,v;

 m := 3*n;

 T["vertices"] := {seq(i,i=2..m+4)};
 F := {
  seq({2+i,2+modp(i+1,m),m+2+modp(i+1,3)},i=0..m-1),
  seq({2+i,m+2+modp(i,3),m+2+modp(i+1,3)},i=0..m-1)
 };
 T["faces"] := F;
 T["max_simplices"] := T["faces"];
 E := map(op,map(f -> {{f[1],f[2]},{f[1],f[3]},{f[2],f[3]}},F));
 T["edges"] := E;
 
 R0 := 3;
 R1 := 1;

 tor := u -> 
  (R0+R1*u[3]*cos(2*Pi*u[2])) *~ [cos(2*Pi*u[1]),sin(2*Pi*u[1]),0] +~
   [0,0,R1*u[3]*sin(2*Pi*u[2])];

 a := table([
  seq(  2+i = evalf([i/3,i/m,1]),i=0..m-1),
  seq(m+2+i = evalf([i/3,i/m,0]),i=0..2)
 ]);

 T["tor_embedding"] := eval(a);

 T["embedding_dim"] := 2;
 T["embedding"] := table([
  seq(v = tor(a[v]),v in T["vertices"])
 ]);

 T["plot"] :=
   `plot/simplicial_complex`(T["vertices"])(T["faces"],2,T["embedding"]);

 tor_arc := proc(u,v)
  local w;
  w := v -~ u;
  w := [w[1] - round(w[1]),w[2] - round(w[2]),w[3]];
  spacecurve(tor(u +~ t *~ w),t=0..1);
 end:

 T["curved_plot"] :=
  display(map(e -> tor_arc(a[e[1]],a[e[2]]),E),
   axes=none,scaling=constrained);

 return eval(T);
end:

