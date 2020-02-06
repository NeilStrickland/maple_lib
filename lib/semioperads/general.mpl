######################################################################
#
# General operad framework.

`check_semi_gamma_args` := proc(J,U,V,is_el_CC)
 local i,k,jj;
 global reason;

 if not type(J,list(nonnegint)) then
  reason := [convert(procname,string),"J is not a list of natural numbers",J];
  return false;
 fi;

 k := nops(J);
 jj := `+`(op(JJ));
 
 if not is_el_CC(k)(U) then
  reason := [convert(procname,string),"U is not in C(k)",eval(U),k];
  return false;
 fi;

 if not (type(V,list) and nops(V) = k) then
  reason := [convert(procname,string),"V is not a list of length k",eval(V),k];
  return false;
 fi;

 for i from 1 to k do 
  if not is_el_CC(J[i])(V[i]) then
   reason := [convert(procname,string),"V[i] is not in C(j[i])",i,j[i],eval(V[i])];
   return false;
  fi;
 od;

 return true;
end;

######################################################################

`check_semi_gamma_axiom` := proc(L,U,V,W,is_el_CC,is_equal_CC,gamma_CC)
 local J,L_,k,jj,ii,H,k0,j0,W0,W_,UV,VW0,VW,UVW0,UVW1;
 global reason;

 if not type(L,list(list(nonnegint))) then
  reason := [convert(procname,string),"L is not a list of lists of natural numbers",L];
  return false;
 fi;

 J := map(nops,L);
 L_ := map(op,L);
 k := nops(J);
 jj := `+`(op(J));
 ii := `+`(op(L_));
 H := [seq(`+`(op(L[k0])),k0=1..k)];
 
 if not is_el_CC(k)(U) then
  reason := [convert(procname,string),"U is not in O(k)",eval(U),k];
  return false;
 fi;

 if not (type(V,list) and nops(V) = k) then
  reason := [convert(procname,string),"V is not a list of length k",eval(V),k];
  return false;
 fi;

 for k0 from 1 to k do 
  if not is_el_CC(J[k0])(V[k0]) then
   reason := [convert(procname,string),"V[k0] is not in O(J[k0])",k0,J[k0],eval(V[k0])];
   return false;
  fi;
 od;

 if not (type(W,list) and nops(W) = k) then
  reason := [convert(procname,string),"W is not a list of length k",eval(W),k];
  return false;
 fi;

 for k0 from 1 to k do
  W0 := W[k0];
  if not (type(W0,list) and nops(W0) = J[k0]) then
   reason := [convert(procname,string),"W[k0] is not a list of length J[k0]",k0,J[k0],W0];
   return false;
  fi;

  for j0 from 1 to J[k0] do
   if not is_el_CC(L[k0][j0])(W[k0][j0]) then
    reason := [convert(procname,string),"W[k0][j0] is not in O(L[k0][j0])",k0,j0,L[k0][j0],eval(W[k0][j0])];
    return false;
   fi;
  od:
 od:

 UV := gamma_CC(J)(U,V);
 if not is_el_CC(jj)(UV) then
  reason := [convert(procname,string),"UV is not in O(jj)",jj,J,eval(U),eval(V),eval(UV)];
  return false;
 fi;

 W_ := map(op,W);
 
 if not `check_semi_gamma_args`(L_,UV,W_,is_el_CC) then
  reason := [convert(procname,string),"invalid arguments to gamma 1",reason];
  return false;
 fi;

 UVW0 := gamma_CC(L_)(UV,W_);
 if not is_el_CC(ii)(UVW0) then
  reason := [convert(procname,string),"UVW0 is not in O(ii)",ii,eval(UVW0)];
  return false;
 fi;

 VW := [];
 for k0 from 1 to k do
  if not `check_semi_gamma_args`(L[k0],V[k0],W[k0],is_el_CC) then
   reason := [convert(procname,string),"invalid arguments to gamma 2",reason];
   return false;
  fi;
  VW0 := gamma_CC(L[k0])(V[k0],W[k0]);
  if not is_el_CC(H[k0])(VW0) then
   reason := [convert(procname,string),"VW[k0] is not in O(H[k0])",k0,H[k0],eval(VW0)];
   return false;
  fi;
  VW := [op(VW),VW0];
 od;

 if not `check_semi_gamma_args`(H,U,VW,is_el_CC) then
  reason := [convert(procname,string),"invalid arguments to gamma 3",reason];
  return false;
 fi;

 UVW1 := gamma_CC(H)(U,VW);
 if not is_el_CC(ii)(UVW1) then
  reason := [convert(procname,string),"UVW1 is not in O(ii)",ii,eval(UVW1)];
  return false;
 fi;

 if not is_equal_CC(ii)(UVW0,UVW1) then
  reason := [convert(procname,string),"UVW0 != UVW1",eval(UVW0),eval(UVW1)];
  return false;
 fi;

 return true;
end;

