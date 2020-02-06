make_boys_complex := proc()
 local T,U,F,p,f,i,L,w,n,P,vb,vn;
 global boys_complex,boys_complex_alt;
 
 T := copy(octahedron_complex):
 for i from 1 to 6 do T["embedding"][i] := boys_corners[i]; od:
 
 T := eval(`triangular_subdivision/simplicial_complex`(T)):
 T := eval(`condense/simplicial_complex`(T)):
 `normalise_embedding/simplicial_complex`(T):
 `star_subdivide/simplicial_complex`(T,{7,8,11}):
 `star_subdivide/simplicial_complex`(T,{16,17,18}):
 `normalise_embedding/simplicial_complex`(T):
 for p from 1 to 4 do 
  T := eval(`triangular_subdivision/simplicial_complex`(T)):
  T := eval(`condense/simplicial_complex`(T)):
  `normalise_embedding/simplicial_complex`(T):
 od:
 F := select(f -> min(op(f)) <= 6,T["max_simplices"]):
 for f in F do 
  `star_subdivide/simplicial_complex`(T,{op(f)} minus {min(op(f))});
 od:
 `normalise_embedding/simplicial_complex`(T):
 for p from 1 to 3 do 
  for i from 1 to 6 do
   L := `link/simplicial_complex`(T,i); 
   w := max(op(L["vertices"]));
   w := `square_refine/simplicial_complex`(T,i,w);
  od:
  `normalise_embedding/simplicial_complex`(T):
 od:

 n := nops(T["vertices"]);
 P := eval(T["embedding"]):
 vb := table():
 vn := table():
 for i from 1 to n do 
  vb[i] := evalf(boys_embedding(P[i]));
  vn[i] := evalf(boys_normal(P[i]));
 od:

 T["boys_embedding"] := eval(vb);
 T["boys_normal"] := eval(vn);

 `set_javascript/simplicial_complex`(T);

 boys_complex := eval(T):

 U := table();
 U["vertices"] := boys_complex["vertices"];
 U["embedding"] := eval(boys_complex["boys_embedding"]);
 U["normal"]    := eval(boys_complex["boys_normal"]);
 U["max_simplices"] := boys_complex["max_simplices"];
 `set_javascript/simplicial_complex`(U);
 
 boys_complex_alt := eval(U);
 
 return eval(T);
end:

save_boys_complex := proc()
 local js_file,T;
 global boys_complex;

 if not(type(boys_complex,table)) then
  make_boys_complex();
 fi;

 save(boys_complex,boys_complex_alt,cat(data_dir,"/boys_complex.m"));

 js_file := cat(data_dir,"/boys_cover_complex.js");
 fprintf(js_file,"%s",boys_complex["javascript"]);
 fclose(js_file);

 js_file := cat(data_dir,"/boys_complex_alt.js");
 fprintf(js_file,"%s",boys_complex_alt["javascript"]);
 fclose(js_file);

end:

