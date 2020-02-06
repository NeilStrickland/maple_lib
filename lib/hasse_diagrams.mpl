`is_element/hasse_diagrams` := (A::set) -> proc(G)
 global reason;
 local D,R;
 
 if not(`is_element/autorel`(A)(G)) then
  reason := ["is_element/hasse_diagrams","G is not a relation on A",G,reason];
  return false;
 fi;

 if not(`is_antisymmetric/autorel`(A)(G)) then
  reason := ["is_element/hasse_diagrams","G is not antisymmetric",G];
  return false;
 fi;

 D := `id/autorel`(A);
 R := `o/autorel`(A)(G,G);
 
 while R <> {} do
  if R intersect G <> {} then
   reason := ["is_element/hasse_diagrams","G has an arrow parallel to a longer path",G,R intersect G];
   return false;
  fi;

  if R intersect D <> {} then
   reason := ["is_element/hasse_diagrams","G has a loop",G,R intersect D];
   return false;
  fi;

  R := `o/autorel`(A)(R,G);
 od;
 
 return true;
end:

`is_element/ranked_hasse_diagrams` := (A::set) -> proc(Gr)
 local G,r,AA,rA,d,A1,r1,a,AA1,G1,M1,M2,Aa,A0,Ma,rMa;
 global reason;

 if not(type(Gr,list) and nops(Gr) = 2) then
  reason := [convert(procname,string),"Gr is not a list of length two",Gr];
  return false;
 fi;

 G,r := op(Gr);
 
 AA := {seq(seq([a,b],b in A),a in A)} minus {seq([a,a],a in A)};

 if not(type(G,set) and G minus AA = {}) then
  reason := [convert(procname,string),"G is not a subset of A^2 minus Delta",G,A];
  return false;
 fi;
 
 if not(type(r,table) and [indices(r)] = map(a -> [a],[op(A)])) then
  reason := [convert(procname,string),"r is not a table indexed by A",r,A];
  return false;
 fi;

 if A = {} then return true; fi;

 rA := map(a -> r[a],A);
 if not(type(rA,list(integer)) and min(op(rA)) = 0) then
  reason := [convert(procname,string),"The values of r are not integers starting from 0",r,A];
  return false;
 fi;

 d := max(rA);
 if rA <> {seq(i,i=0..d)} then
  reason := [convert(procname,string),"The values of r do not form an interval starting from 0",r,A];
  return false;
 fi;

 if d = 0 then
  if G = {} then
   return true;
  else
   reason := [convert(procname,string),"All ranks are zero but G is not empty",G];
   return false;
  fi;
 fi;

 A1 := select(a -> (r[a] < d),A);
 r1 := table();
 for a in A1 do r1[a] := r[a]; od;
 AA1 := {seq(seq([a,b],b in A1),a in A1)} minus {seq([a,a],a in A1)};
 G1 := G intersect AA1;

 if not(`is_element/ranked_hasse_diagrams`(A1)([G1,r1])) then
  return false;
 fi;

 M1 := NULL;
 for a in A1 do
  Aa := select(b -> member([a,b],G1),A1);
  if Aa = {} then M1 := M1,a; fi;
 od:
 M1 := {M1};
 M2 := select(a -> (r[a] = d-1),M1);

 A0 := A minus A1;

 for a in A0 do
  Ma := select(b -> member([b,a],G),A);
  rMa := map(b -> r[b],Ma);
  if not(member(d-1,rMa)) then
   reason := [convert(procname,string),"a has rank d but does not cover anything of rank d-1",a,d,Ma];
   return false;
  fi;
 od:
end:
