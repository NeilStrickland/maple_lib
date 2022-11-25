make_dihedral := proc(n)
 local G,m,c;

 G["rotation_order"] := n;
 G["order"] := 2*n;
 G["elements"] := [seq(seq([m,c],c=0..n-1),m in [1,-1])];
 G["id"] := [1,0];
 G["o"] := (g,h) -> [g[1]*h[1],modp(g[1]*h[2]+g[2],n)];
 G["inv"] := (g) -> [g[1],modp(-g[1]*g[2],n)];

 return eval(G);
end: