flat_torus_complex := proc(n::posint,m::posint)
 local f,g,T,V,E,F,R,r;

 f := (i) -> modp(i+1,n);
 g := (j) -> modp(j+1,m);
 
 V := [seq(seq([i,j],j=0..m-1),i=0..n-1)];
 E := [seq(seq([[i,j],[f(i),j]],j=0..m-1),i=0..n-1),
       seq(seq([[i,j],[i,g(j)]],j=0..m-1),i=0..n-1),
       seq(seq([[i,j],[f(i),g(j)]],j=0..m-1),i=0..n-1)];
 F := [seq(seq([[i,j],[f(i),j],[f(i),g(j)]],j=0..m-1),i=0..n-1),
       seq(seq([[i,j],[i,g(j)],[f(i),g(j)]],j=0..m-1),i=0..n-1)];

 T := table([]);

 T["vertices"] := V;
 T["edges"] := E;
 T["faces"] := F;
 T["max_simplices"] := F;
 T["simplices"] := [map(v -> [v],V),op(E),op(F)];

 R := 3;
 r := 1;

 T["embedding_dim"] := 3;
 T["embedding"] :=
  table([seq(seq([i,j] = evalf(torus_embedding(R,r)(i/n,j/m)),j=0..m-1),i=0..n-1)]);

 T["plot"] := `plot/simplicial_complex`(T["vertices"])(T["faces"],3,T["embedding"]);

 return eval(T);

end: