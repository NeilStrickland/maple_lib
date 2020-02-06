
make_complex_projective_space := proc(n::nonnegint)
 local T,x,i;

 T := table([]):
 T["name"] := sprintf("CP^%d",n);
 T["dimension"] := 2*n;
 T["cohomology_gens"] := tdeg(x);
 T["cohomology_degrees"] := table([x = 2]);
 T["cohomology_rels"] := [x^(n+1)];
 T["cohomology_basis"] := [seq(x^i,i=0..n)];
 T["cohomology_graded_basis"] := table([]):
 for i from 0 to 2*n do
  T["cohomology_graded_basis"][i] := 
   `if`(modp(i,2)=0,[x^(i/2)],[]);
 od:

 return eval(T);
end:
