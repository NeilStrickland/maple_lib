rename_cohomology_gens := proc(T0::table,u::list)
 local u0,n0,r,T,i;

 u0 := [op(T0["cohomology_gens"])];
 n0 := nops(u0);

 if nops(u) <> n0 then
  error("Incorect number of cohomology generators");
 fi;

 r := [seq(u0[i] = u[i],i=1..n0)];

 T := copy(T0);
 T["cohomology_gens"] := subs(r,T0["cohomology_gens"]);
 T["cohomology_rels"] := subs(r,T0["cohomology_rels"]);
 T["cohomology_degrees"] := table([]):
 for i from 1 to n0 do 
  T["cohomology_degrees"][u[i]] := 
   T0["cohomology_degrees"][u0[i]];
 od;
 T["cohomology_basis"] := subs(r,T0["cohomology_basis"]);
 for i from 0 to T["dimension"] do 
  T["cohomology_graded_basis"][i] := 
   subs(r,T["cohomology_graded_basis"][i]); 
 od:

 return eval(T);
end:


make_product_space := proc(T0,T1)
 local T,d0,d1,B0,B1,B,i0,i1,u0,u1,x,i;
 T := table():
 
 T["name"] := sprintf("%s x %s",T0["name"],T1["name"]);
 d0 := T0["dimension"];
 d1 := T1["dimension"];
 T["dimension"] := d0+d1;
 T["cohomology_gens"] := tdeg(op(T0["cohomology_gens"]),
                              op(T1["cohomology_gens"]));
 T["cohomology_rels"] := [op(T0["cohomology_rels"]),
                          op(T1["cohomology_rels"])];
 T["cohomology_degrees"] := table([]);
 for x in T0["cohomology_gens"] do 
  T["cohomology_degrees"][x] := T0["cohomology_degrees"][x];
 od:
 for x in T1["cohomology_gens"] do 
  T["cohomology_degrees"][x] := T1["cohomology_degrees"][x];
 od:

 T["cohomology_basis"] := [seq(seq(u0*u1,u0 in T0["cohomology_basis"]),
                                         u1 in T1["cohomology_basis"])];

 B0 := T0["cohomology_graded_basis"]:
 B1 := T1["cohomology_graded_basis"]:
 B := table():

 for i from 0 to d0+d1 do
  B[i] := NULL:

  for i0 from max(0,i-d1) to min(i,d0) do
   i1 := i - i0; 
   B[i] := B[i],seq(seq(u0*u1,u0 in B0[i0]),u1 in B1[i1]);
  od:
 od;

 T["cohomology_graded_basis"] := eval(B):

 return eval(T);
end:

