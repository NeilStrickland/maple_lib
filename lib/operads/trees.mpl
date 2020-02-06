######################################################################
 
`eta/trees` := (A::set) -> `if`(nops(A)=1,{A},FAIL);

`gamma/trees` := (A::set,B::set) -> (p) -> proc(UU,TT)
 local F,U,V,VV,b;

 F := fibres(A,B)(p);

 VV := NULL;
 for U in UU do
  V := `union`(seq(F[b],b in U));
  if V <> {} then VV := VV,V; fi;
 od;

 for b in B do 
  VV := VV,op(TT[b]);
 od;

 VV := sort(map(sort,{VV}));

 return VV;
end;
