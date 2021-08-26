mobius_complex := proc()
 local T,V,E,F,R,r,v,a,mob,mob_arc,i,e;
 
 V := [seq(seq([i,a],a=0..2),i=0..1)];
 F := [
  seq([[0,a],[0,modp(a+1,3)],[1,a]],a=0..2),
  seq([[0,a],[0,modp(a+1,3)],[1,modp(a+1,3)]],a=0..2),
  seq([[0,a],[1,modp(a+1,3)],[1,modp(a+2,3)]],a=0..2) 
 ];

 E := map(f -> ([f[1],f[2]],[f[1],f[3]],[f[2],f[3]]),F);

 T := table([]);

 T["vertices"] := V;
 T["edges"] := E;
 T["faces"] := F;
 T["max_simplices"] := T["faces"];
 
 T["all_simplices"] := [map(v -> [v],V),op(E),op(F)];

 v := table():
 for a from 0 to 2 do 
  v[0,a] := [a/6,0];
  v[1,a] := [a/3,1];
 od:

 R := 1;
 r := 1/3:
 mob := mobius_embedding(R,r);
 
 mob_arc := mobius_arc(R,r);

 T["plot"] :=
  display(
   spacecurve(mob(t,1),t=0..1,colour=blue),
   plot3d(mob(t,u),t=0..1,u=0..1,style=wireframe,colour="LightGray"),
   seq(mob_arc(op(v[op(e[1])]),op(v[op(e[2])]),colour=red),e in E),
   axes=none,scaling=constrained
  );

 return eval(T);
end():

flat_mobius_complex := proc(n::posint)
 local f,g,T,V,E,F,r,v,a,i;

 f := (i) -> modp(i+1,4*n+2);
 g := (i) -> modp(i+2*n+3/2+(-1)^i/2,4*n+2);
 
 V := [seq(i,i=0..4*n+1)];
 E := [seq([i,f(i)],i=0..4*n+1),seq([i,g(i)],i=0..4*n+1)];
 F := [seq([i,f(i),g(i)],i=0..4*n+1)];

 T := table([]);

 T["vertices"] := V;
 T["edges"] := E;
 T["faces"] := F;
 T["max_simplices"] := T["faces"];
 T["all_simplices"] := [map(v -> [v],V),op(E),op(F)];

 T["embedding_dim"] := 3;
 T["embedding"] := table([seq(i = evalf(mobius_embedding(0.2)(i/(4*n+2),1)),i=0..4*n+1)]);

 T["plot"] := `plot/raw_simplicial_complex`(T["vertices"])(T["faces"],3,T["embedding"]);

 return eval(T);

end: