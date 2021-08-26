######################################################################
#
# General operad framework.

`check_gamma_args` := proc(A,B,p,U,V,is_el_CC)
 local F,b;
 global reason;

 if not type(A,set) then
  reason := [convert(procname,string),"A is not a set",A];
  return false;
 fi;
 if not type(B,set) then
  reason := [convert(procname,string),"B is not a set",B];
  return false;
 fi;

 if not `is_element/maps`(A,B)(p) then
  reason := [convert(procname,string),"not a map from A to B",A,B,reason];
  return false;
 fi;

 F := fibres(A,B)(p);

 if not is_el_CC(B)(U) then
  reason := [convert(procname,string),"U is not in C(B)",eval(U),B];
  return false;
 fi;

 if not type(V,table) then
  reason := [convert(procname,string),"V is not a table",eval(V)];
  return false;
 fi;

 if map(op,{indices(V)}) <> B then
  reason := [convert(procname,string),"V is not indexed by B",eval(V),B];
  return false;
 fi;

 for b in B do
  if not is_el_CC(F[b])(V[b]) then
   reason := [convert(procname,string),"V[b] is not in C(F[b])",b,eval(V[b]),eval(F[b])];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`check_gamma_axiom` := proc(A,B,C,p,q,U,V,W,is_el_CC,is_equal_CC,gamma_CC)
# local a,b,c,qp,Fp,Fq,Fqp,UV,VW,UVW0,UVW1,W0,p0;
# global reason,check_gamma_axiom_args;
 local a,b,c,qp,Fp,Fq,Fqp,UV,VW,W0,p0;
 global UVW0,UVW1,reason,check_gamma_axiom_args;

 check_gamma_axiom_args := [args];

 if not type(A,set) then
  reason := [convert(procname,string),"A is not a set",eval(A)];
  return false;
 fi;
 if not type(B,set) then
  reason := [convert(procname,string),"B is not a set",eval(B)];
  return false;
 fi;
 if not type(C,set) then
  reason := [convert(procname,string),"C is not a set",eval(C)];
  return false;
 fi;

 if not `is_element/maps`(A,B)(p) then
  reason := [convert(procname,string),"p is not a map from A to B",eval(p),A,B,reason];
  return false;
 fi;

 if not `is_element/maps`(B,C)(q) then
  reason := [convert(procname,string),"q is not a map from B to C",eval(q),B,C,reason];
  return false;
 fi;

 qp := `compose/maps`(A,B,C)(p,q);

 Fp := fibres(A,B)(p);
 Fq := fibres(B,C)(q);
 Fqp := fibres(A,C)(qp);

 if not is_el_CC(C)(U) then
  reason := [convert(procname,string),"U is not in O(C)",eval(U),C];
  return false;
 fi;

 if not type(V,table) then
  reason := [convert(procname,string),"V is not a table",eval(V)];
  return false;
 fi;

 if map(op,{indices(V)}) <> C then
  reason := [convert(procname,string),"V is not indexed by C",eval(V),C];
  return false;
 fi;

 for c in C do
  if not is_el_CC(Fq[c])(V[c]) then
   reason := [convert(procname,string),"V[c] is not in O(Fq[c])",c,eval(V[c]),eval(Fq[c])];
   return false;
  fi;
 od;

 if not type(W,table) then
  reason := [convert(procname,string),"W is not a table",eval(W)];
  return false;
 fi;

 if map(op,{indices(W)}) <> B then
  reason := [convert(procname,string),"W is not indexed by B",eval(W),B];
  return false;
 fi;

 for b in B do
  if not is_el_CC(Fp[b])(W[b]) then
   reason := [convert(procname,string),"W[b] is not in O(Fp[b])",b,eval(W[b]),eval(Fp[b])];
   return false;
  fi;
 od;

 UV := gamma_CC(B,C)(q)(U,V);
 if not is_el_CC(B)(UV) then
  reason := [convert(procname,string),"UV is not in O(B)",eval(UV),B,C,eval(q),eval(U),eval(V)];
  return false;
 fi;

 if not `check_gamma_args`(A,B,p,UV,W,is_el_CC) then
  reason := [convert(procname,string),"invalid arguments to gamma 1",reason];
  return false;
 fi;

 UVW0 := gamma_CC(A,B)(p)(UV,W);
 if not is_el_CC(A)(UVW0) then
  reason := [convert(procname,string),"UVW0 is not in C(A)",eval(UVW0),A];
  return false;
 fi;

 VW := table();
 for c in C do
  W0 := table();
  p0 := table();
  for b in Fq[c] do W0[b] := W[b]; od;
  for a in Fqp[c] do p0[a] := p[a]; od;
  if not `check_gamma_args`(Fqp[c],Fq[c],p0,V[c],W0,is_el_CC) then
   reason := [convert(procname,string),"invalid arguments to gamma 2",reason];
   return false;
  fi;
  VW[c] := gamma_CC(Fqp[c],Fq[c])(p0)(V[c],W0);
 od;

 if not `check_gamma_args`(A,C,qp,U,VW,is_el_CC) then
  reason := [convert(procname,string),"invalid arguments to gamma 3",reason];
  return false;
 fi;

 UVW1 := gamma_CC(A,C)(qp)(U,VW);
 if not is_el_CC(A)(UVW1) then
  reason := [convert(procname,string),"UVW1 is not in C(A)",eval(UVW1),A];
  return false;
 fi;

 if not is_equal_CC(A)(UVW0,UVW1) then
  reason := [convert(procname,string),"UVW0 != UVW1",eval(UVW0),eval(UVW1)];
  return false;
 fi;

 return true;
end;

######################################################################

check_operad_morphism_axiom :=
 proc(A,B,p,U,V,
      is_el_CC,is_equal_CC,gamma_CC,
      is_el_DD,is_equal_DD,gamma_DD,
      phi)

 local b,Fp,UV,U1,V1,UV1,UV2;

 global reason,check_operad_morphism_axiom_args;

 check_operad_morphism_axiom_args := [args];

 if not type(A,set) then
  reason := [convert(procname,string),"A is not a set",eval(A)];
  return false;
 fi;

 if not type(B,set) then
  reason := [convert(procname,string),"B is not a set",eval(B)];
  return false;
 fi;

 if not `is_element/maps`(A,B)(p) then
  reason := [convert(procname,string),"p is not a map from A to B",eval(p),A,B,reason];
  return false;
 fi;

 Fp := fibres(A,B)(p);

 if not is_el_CC(B)(U) then
  reason := [convert(procname,string),"U is not in C(B)",eval(U),B];
  return false;
 fi;

 if not type(V,table) then
  reason := [convert(procname,string),"V is not a table",eval(V)];
  return false;
 fi;

 if map(op,{indices(V)}) <> B then
  reason := [convert(procname,string),"V is not indexed by B",eval(V),B];
  return false;
 fi;

 for b in B do
  if not is_el_CC(Fp[b])(V[b]) then
   reason := [convert(procname,string),"V[b] is not in C(Fp[b])",b,eval(V[b]),eval(Fp[b])];
   return false;
  fi;
 od;

 UV := gamma_CC(A,B)(p)(U,V);
 if not is_el_CC(A)(UV) then
  reason := [convert(procname,string),"UV is not in C(A)",eval(UV),A,B,eval(p),eval(U),eval(V)];
  return false;
 fi;

 U1 := phi(B)(U);
 if not is_el_DD(B)(U1) then
  reason := [convert(procname,string),"phi(U) is not in D(B)",eval(U1),B];
  return false;
 fi;

 V1 := table();
 for b in B do
  V1[b] := phi(Fp[b])(V[b]);
  if not is_el_DD(Fp[b])(V1[b]) then
   reason := [convert(procname,string),"phi(V[b]) is not in D(Fp[b])",eval(V1),b,eval(Fp[b])];
   return false;
  fi;
 od;

 UV1 := gamma_DD(A,B)(p)(U1,V1);
 if not is_el_DD(A)(UV1) then
  reason := [convert(procname,string),"UV1 is not in D(A)",eval(UV1),A];
  return false;
 fi;

 UV2 := phi(A)(UV);
 if not is_el_DD(A)(UV1) then
  reason := [convert(procname,string),"phi(UV) is not in D(A)",eval(UV2),A];
  return false;
 fi;

 if not(is_equal_DD(A)(UV1,UV2)) then
  reason := [convert(procname,string),"UV1 != UV2",eval(UV1),eval(UV2)];
  return false;
 fi;

 return true;
end:

check_operad_morphism_axiom_globalise := proc()
 global check_operad_morphism_axiom_args,
         A,B,p,U,V,
         is_el_CC,is_equal_CC,gamma_CC,
         is_el_DD,is_equal_DD,gamma_DD,
         phi;
 local ARGS;
 ARGS := check_operad_morphism_axiom_args;
 
 A               := eval(ARGS[ 1]);
 B		 := eval(ARGS[ 2]);
 p		 := eval(ARGS[ 3]);
 U		 := eval(ARGS[ 4]);
 V		 := eval(ARGS[ 5]);
 is_el_CC	 := eval(ARGS[ 6]);
 is_equal_CC	 := eval(ARGS[ 7]);
 gamma_CC	 := eval(ARGS[ 8]);
 is_el_DD	 := eval(ARGS[ 9]);
 is_equal_DD	 := eval(ARGS[10]);
 gamma_DD	 := eval(ARGS[11]);
 phi 		 := eval(ARGS[12]);
 NULL;
end:

######################################################################

# An operad E consists of sets E(A) for each finite set A, functorial
# for bijections of A.  We have formulated the definitions in such a
# way that this functoriality is determined by the rest of the
# structure.  The code here implements this.

`action/operad` := (gen_name,eta,gamma) -> (A::set,B::set) -> (f) -> proc(x)
 local f_inv,e,a;

 f_inv := table();
 e := table();
 for a in A do
  f_inv[f[a]] := a;
  e[a] := eta({f[a]});
 od;
 return gamma(B,A)(f_inv)(x,e);
end;

######################################################################

extend_gamma_linear := (g0) -> (A::set,B::set) -> (p) -> proc(y,x)
 local c,y1,F,BL,M,b,t,z,m,mt,u,i;
 
 if y = 0 then
  return 0;
 elif type(y,`+`) then
  return map(t -> extend_gamma_linear(g0)(A,B)(p)(t,x),y);
 fi;

 if type(y,`*`) then
  c,y1 := selectremove(type,y,integer);
 else
  c := 1;
  y1 := y;
 fi;

 F := fibres(A,B)(p);

 BL := sort([op(B)]);
 M := [[1]];
 for b in BL do
  t := map(coeff_split,sum_terms(x[b]));
  M := [seq(seq([m[1] * u[1],seq(m[i],i=2..nops(m)),u[2]],u in t),m in M)];
 od:

 z := 0;

 for m in M do
  mt := table([seq(BL[i]=m[i+1],i=1..nops(BL))]);
  z := z + c * m[1] * g0(A,B)(p)(y1,mt);
 od;

 return z;

end;