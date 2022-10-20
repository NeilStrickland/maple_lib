######################################################################
# General circle operad framework.

`check_semi_circ_args` := proc(i,m,n,U,V,is_el_CC)
 global reason;

 if not (type(i,posint) and
         type(m,nonnegint) and
	 type(n,nonnegint) and
	 i <= m) then
  reason := [convert(procname,string),
   "numbers (i,m,n) do not satisfy 0 < i <= m; 0 <= n",i,m,n];
  return false;
 fi;

 if not is_el_CC(m)(U) then
  reason := [convert(procname,string),"U is not in C(m)",eval(U),m];
  return false;
 fi;

 if not is_el_CC(n)(U) then
  reason := [convert(procname,string),"V is not in C(n)",eval(V),n];
  return false;
 fi;

 return true;
end;

######################################################################

`check_semi_circ_axiom_nested` :=
 proc(i,j,l,m,n,U,V,W,is_el_CC,is_equal_CC,circ_CC)
 local UV,VW,UVW0,UVW1;
 global reason;

 if not (type(i,posint) and
         type(j,posint) and
	 type(l,nonnegint) and
	 type(m,nonnegint) and
	 type(n,nonnegint) and
	 i <= l and
	 j <= m) then 
  reason := [convert(procname,string),
   "numbers (i,j,l,m,n) do not satisfy 0 < i <= l; 0 < j <= m; 0 <= n",
   i,j,l,m,n];
  return false;
 fi;

 if not is_el_CC(l)(U) then
  reason := [convert(procname,string),"U is not in O(l)",l,eval(U)];
  return false;
 fi;

 if not is_el_CC(m)(V) then
  reason := [convert(procname,string),"V is not in O(m)",m,eval(V)];
  return false;
 fi;

 if not is_el_CC(n)(W) then
  reason := [convert(procname,string),"W is not in O(n)",n,eval(W)];
  return false;
 fi;

 UV := circ_CC(i,l,m)(U,V);

 if not is_el_CC(l+m-1)(UV) then
  reason := [convert(procname,string),"U o_i V is not in O(l+m-1)",i,l,m,eval(U),eval(V),eval(UV)];
  return false;
 fi;

 VW := circ_CC(j,m,n)(V,W);

 if not is_el_CC(m+n-1)(VW) then
  reason := [convert(procname,string),"V o_j W is not in O(m+n-1)",j,m,n,eval(VW)];
  return false;
 fi;

 UVW0 := circ_CC(i,l,m+n-1)(U,VW);

 if not is_el_CC(l+m+n-2)(UVW0) then
  reason := [convert(procname,string),"U o_i (V o_j W) is not in O(l+m+n-2)",i,j,l,m,n,eval(UVW0)];
  return false;
 fi;

 UVW1 := circ_CC(i+j-1,l+m-1,n)(UV,W);

 if not is_el_CC(l+m+n-2)(UVW1) then
  reason := [convert(procname,string),"(U o_i V) o_(i+j-1) W is not in O(l+m+n-2)",i,j,l,m,n,eval(UVW1)];
  return false;
 fi;

 if not is_equal_CC(l+m+n-2)(UVW0,UVW1) then
  reason := [convert(procname,string),"UVW0 != UVW1",eval(UVW0),eval(UVW1)];
  return false;
 fi;

 return true;
end;

`check_semi_circ_axiom_disjoint` :=
 proc(i,k,l,m,n,U,V,W,is_el_CC,is_equal_CC,circ_CC)
 local UV,UW,UVW,UWV;
 global reason;

 if not (type(i,posint) and
         type(k,posint) and
	 type(l,nonnegint) and
	 type(m,nonnegint) and
	 type(n,nonnegint) and
	 i < k and
	 k <= l) then 
  reason := [convert(procname,string),
   "numbers (i,k,l,m,n) do not satisfy 0 < i < k <= l; 0 < j <= m; 0 <= n",
   i,k,l,m,n];
  return false;
 fi;

 if not is_el_CC(l)(U) then
  reason := [convert(procname,string),"U is not in O(l)",l,eval(U)];
  return false;
 fi;

 if not is_el_CC(m)(V) then
  reason := [convert(procname,string),"V is not in O(m)",m,eval(V)];
  return false;
 fi;

 if not is_el_CC(n)(W) then
  reason := [convert(procname,string),"W is not in O(n)",n,eval(W)];
  return false;
 fi;

 UV := circ_CC(i,l,m)(U,V);

 if not is_el_CC(l+m-1)(UV) then
  reason := [convert(procname,string),"U o_i V is not in O(l+m-1)",i,l,m,eval(U),eval(V),eval(UV)];
  return false;
 fi;

 UW := circ_CC(k,l,n)(U,W);

 if not is_el_CC(l+n-1)(UW) then
  reason := [convert(procname,string),"U o_k W is not in O(l+n-1)",k,l,n,eval(UW)];
  return false;
 fi;

 UVW := circ_CC(k+m-1,l+m-1,n)(UV,W);

 if not is_el_CC(l+m+n-2)(UVW) then
  reason := [convert(procname,string),"(U o_i V) o_(k+m-1) W is not in O(l+m+n-2)",i,k,l,m,n,eval(UVW)];
  return false;
 fi;

 UWV := circ_CC(i,l+n-1,m)(UW,V);

 if not is_el_CC(l+m+n-2)(UWV) then
  reason := [convert(procname,string),"(U o_k W) o_i V is not in O(l+m+n-2)",i,k,l,m,n,eval(UWV)];
  return false;
 fi;

 if not is_equal_CC(l+m+n-2)(UVW,UWV) then
  reason := [convert(procname,string),"UVW != UWV",eval(UVW),eval(UWV)];
  return false;
 fi;

 return true;
end;


