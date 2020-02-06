`find_bases/homology` := proc(H)
 local dM,dZM,nC,nZ,nB,nH,d,d_max,i,j,r,LM,ZM,BZM,BM,HZM,HM,
  S,M0,M1,M2,M3,pivots,non_pivots;

 dM := H[differential_matrix]:
 nC := eval(H['chain_number']);
 d_max := H['dim'];
 for d from 0 to d_max do
  if d = 0 then
   LM[0] := Matrix(nC[0],0):
   ZM[0] := IdentityMatrix(nC[0]):
   nZ[0] := nC[0];
  else
   ZM[d] := [op(NullSpace(dM[d]))];
   nZ[d] := nops(ZM[d]);
   ZM[d] := Matrix(nC[d],nZ[d],ZM[d]);
  fi;

  if d = d_max then
   BZM[d] := Matrix(nZ[d],0);
   BM[d] := Matrix(nC[d],0);
   nB[d] := 0;
   HZM[d] := IdentityMatrix(nZ[d]);
   HM[d] := ZM[d];
   nH[d] := nZ[d];
  else
   dZM[d+1] := LinearSolve(ZM[d],dM[d+1]);
   S := LUDecomposition(Transpose(dZM[d+1]),output=['P','L','U1','R']):
   M0,M1 := Transpose(S[4]),Transpose(S[1].S[2].S[3]):
   pivots := {}:
   j := 1:
   i := 1:
   while i <= nC[d+1] do
    while j <= nZ[d] and M0[j,i] = 0 do j := j+1; od;
    if j <= nZ[d] then pivots := {op(pivots),j}; fi;
    i := i+1;
   od:
   r := nops(pivots);
   nB[d] := r;
   nH[d] := nZ[d]-r;

   non_pivots := {seq(j,j=1..nZ[d])} minus pivots;

   M2 := Matrix(nZ[d],nZ[d]-r);
   for i from 1 to nZ[d]-r do M2[non_pivots[i],i] := 1; od:
   M3 := SubMatrix(M0,1..nZ[d],1..r);
   HM[d] := ZM[d] . M2;
   BM[d] := ZM[d] . M3;
   ZM[d] := <HM[d]|BM[d]>;
   HZM[d] := <IdentityMatrix(nH[d]),Matrix(nZ[d]-nH[d],nH[d])>;
   BZM[d] := <Matrix(nZ[d]-nB[d],nB[d]),IdentityMatrix(nB[d])>;
   LM[d+1] := (1/M1).<IdentityMatrix(r),Matrix(nC[d+1]-r,r)>;
  fi;
 od:

 H['cycle_matrix'] := eval(ZM);
 H['boundary_matrix'] := eval(BM);
 H['boundary_cycle_matrix'] := eval(BZM);
 H['boundary_lift_matrix'] := eval(LM);
 H['homology_matrix'] := eval(HM);
 H['homology_cycle_matrix'] := eval(HZM);
 
 H['cycle_number'] := eval(nZ);
 H['boundary_number'] := eval(nB);
 H['homology_number'] := eval(nH);

 return NULL;
end:

######################################################################

`check_bases/homology` := proc(H)
 local dM,dZM,nC,nZ,nB,nH,d,d_max,i,j,r,LM,ZM,BZM,BM,HZM,HM,
  checks;

 nC  := eval(H['chain_number']);
 nZ  := eval(H['cycle_number']);
 nB  := eval(H['boundary_number']);
 nH  := eval(H['homology_number']);
 ZM  := eval(H['cycle_matrix']);
 BM  := eval(H['boundary_matrix']);
 BZM := eval(H['boundary_cycle_matrix']);
 LM  := eval(H['boundary_lift_matrix']);
 HM  := eval(H['homology_matrix']);
 HZM := eval(H['homology_cycle_matrix']);
 d_max := H['dim'];
 dM := eval(H['differential_matrix']):

 for d from 0 to d_max do 
  checks := [
   [Dimension( ZM[d])] = [nC[d],nZ[d]],
   [Dimension( BM[d])] = [nC[d],nB[d]],
   [Dimension(BZM[d])] = [nZ[d],nB[d]],
   [Dimension( LM[d])] = [nC[d],`if`(d>0,nB[d-1],0)],
   [Dimension( HM[d])] = [nC[d],nH[d]],
   [Dimension(HZM[d])] = [nZ[d],nH[d]],
   nC[d] = nH[d] + nB[d] + `if`(d>0,nB[d-1],0),
   nH[d] = H['betti_number'][d]
  ];

  if not(`and`(op(map(evalb,checks)))) then
   print([d,checks]);
   return false;
  fi;
 od:

 for d from 1 to d_max do
  checks := [
   Equal(dM[d] . ZM[d],Matrix(nC[d-1],nZ[d])),
   Equal(dM[d] . BM[d],Matrix(nC[d-1],nB[d])),
   Equal(dM[d] . LM[d],BM[d-1]),
   Rank(dM[d]) = nB[d-1],
   Rank(ZM[d]) = nZ[d],
   Rank(BM[d]) = nB[d],
   Rank(HM[d]) = nH[d],
   Rank(BZM[d]) = nB[d],
   Rank(HZM[d]) = nH[d]
  ];
  if not(`and`(op(map(evalb,checks)))) then
   print([d,checks]);
   return false;
  fi;
 od:
 return true;
end:

######################################################################

`vec/chains` := (H) -> (d::nonnegint) -> proc(u)
 local v,i,uc,uv;

 if u = 0 then 
  return Vector(H['chain_number'][d]);
 elif type(u,`+`) then
  # Slightly convoluted because of funny behaviour of + on vectors
  return `+`(op(map(`vec/chains`(H)(d),[op(u)])));
 elif type(u,`*`) then
  uc,uv := selectremove(type,u,rational);
  if uc <> 1 then
   return uc * `vec/chains`(H)(d)(uv);
  fi;
 elif type(u,specfunc(chain)) then
  v := Vector(H['chain_number'][d]);
  i := H['chain_index'][d][u];
  v[i] := 1;
  return v;
 fi;
 return 'procname'(args);
end:

`vec/cycles/vec` := (H) -> (d::nonnegint) -> proc(v)
 LinearSolve(H['cycle_matrix'][d],v);
end:

`vec/cycles` := (H) -> (d::nonnegint) -> proc(u)
 `vec/cycles/vec`(H)(d)(`vec/chains`(H)(d)(u));
end:

`vec/homology/vec` := (H) -> (d::nonnegint) -> proc(v)
 SubVector(LinearSolve(H['cycle_matrix'][d],v),1..H['homology_number'][d]);
end:

`vec/homology` := (H) -> (d::nonnegint) -> proc(u)
 `vec/homology/vec`(H)(d)(`vec/chains`(H)(d)(u));
end:

`basis/homology` := (H) -> proc(d::nonnegint)
 convert(Transpose(H['homology_matrix'][d]) . Vector(H['chains'][d]),list);
end:

######################################################################

is_homology_sphere := proc(H,d_)
 local d,d1,b,i;
 d1 := H['dim'];
 if nargs > 1 then 
  d := d_;
 else 
  d := d1;
 fi;
 b := eval(H['betti_number']);
 
 if d = -1 then # The -1 sphere is empty
  return evalb(d1 = -1);
 fi;

 for i from 0 to d1 do 
  if i <> 0 and i <> d and b[i] <> 0 then
   return false;
  fi; 
 od;

 if d = 0 then 
  return evalb(b[0] = 2);
 else
  return evalb(b[0] = 1 and b[d] = 1);
 fi;
end:

######################################################################

is_homology_bouquet := proc(H,d,r)
 local d1,b,i;
 d1 := H['dim'];
 b := eval(H['betti_number']);
 
 for i from 0 to d1 do 
  if i <> 0 and i <> d and b[i] <> 0 then
   return false;
  fi; 
 od;

 if d = 0 then 
  return evalb(b[0] = r+1);
 else
  return evalb(b[0] = 1 and b[d] = r);
 fi;
end:

######################################################################

is_homology_acyclic := proc(H)
 local d1,b,i;
 d1 := H['dim'];
 if d1 = -1 then return false; fi;
 
 b := eval(H['betti_number']);
 if b[0] <> 1 then return false; fi;
 
 for i from 1 to d1 do 
  if b[i] <> 0 then
   return false;
  fi; 
 od;

 return true;
end:


