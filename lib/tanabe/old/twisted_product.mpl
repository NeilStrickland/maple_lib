# This code sets up a toy model of the nonstandard product structure
# on the HKR character ring for V x V, where V is the groupoid of
# finite-dimensional F-vector spaces.

# We fix a number d > 0 (which should really be infinity).
# We consider the set A1 of tables indexed by natural numbers u < d,
# and the set A2 indexed by pairs (u,v) with u+v < d.  These sets
# have products called `star/A1` and `star/A2`.  The first is given by
# the following rule: `star/A1`(f,g)[u] is the sum of all terms
# c1[u0,u1] * f[u0] * g[u1], where u0+u1 = u, and c1[u0,u1] is the
# number of splittings of F^u as a direct sum of subspaces of
# dimensions u0 and u1.
#
# Similarly, `star/A2`(f,g)[u,v] is a sum of terms
# c2[u0,v0,u1,v1] * f[u0,v0] * g[u1,v1] where
# (u0,v0) + (u1,v1) = (u,v) and
# c2[u0,v0,u1,v1] is c1[u0,u1] times c1[v0,v1] times
# q^(u0*v1+2*u1*v0).  This final factor is inserted to ensure that
# the coproduct map psi : A1 -> A2 (given by psi(f)[u,v]=f[u+v])
# is a ring map.

d := 10;

grassmann_count := (q) -> (n,d) ->
 mul(q^(n-i)-1,i=0..d-1)/mul(q^(d-i)-1,i=0..d-1);

splitting_count := (q) -> (n,m) ->
 grassmann_count(q)(n+m,n) * q^(n*m);

######################################################################

`is_element/A1` := proc(f)
 local u,L;
 
 if not(type(f,table)) then
  return false;
 fi;

 L := [seq([u],u=0..d-1)];

 if [indices(f)] <> L then
  return false;
 fi;

 return true;
end:

`is_equal/A1` := proc(f,g)
 local u;
 
 for u from 0 to d-1 do
  if simplify(f[u]-g[u]) <> 0 then
   return false;
  fi;
 od;
 return true;
end:

`to_list/A1` := (f) -> [seq(f[u],u=0..d-1)]:
`from_symbol/A1` := (f) -> table([seq(u=f[u],u=0..d-1)]);

`zero/A1`  := table([seq(u=0,u=0..d-1)]):
`one/A1`   := table([seq(u=1,u=0..d-1)]):
`delta/A1` := table([seq(u=`if`(u=0,1,0),u=0..d-1)]):

`plus/A1` := proc(f,g)
 table([seq(u = f[u]+g[u],u=0..d-1)]);
end:

`minus/A1` := proc(f,g)
 table([seq(u = f[u]-g[u],u=0..d-1)]);
end:

`dot/A1` := proc(f,g)
 table([seq(u = f[u]*g[u],u=0..d-1)]);
end:

`scalar_times/A1` := proc(c,f)
 table([seq(u = c*f[u],u=0..d-1)]);
end:

`star/A1` := proc(f,g)
 local h,u,u0,u1;
 h := table();
 for u from 0 to d-1 do
  h[u] := 0;
 od;

 for u0 from 0 to d-1 do 
  for u1 from 0 to d-1-u0 do
   h[u0+u1] := h[u0+u1] + splitting_count(q)(u0,u1)*f[u0]*g[u1];
  od;
 od:

 return eval(h);
end:

######################################################################

`is_element/A2` := proc(f)
 local u,L;
 
 if not(type(f,table)) then
  return false;
 fi;

 L := [seq(seq([u,v],v=0..d-1-u),u=0..d-1)];

 if [indices(f)] <> L then
  return false;
 fi;

 return true;
end:

`is_equal/A2` := proc(f,g)
 local u,v;
 
 for u from 0 to d-1 do
  for v from 0 to d-1-u do
   if simplify(f[u,v]-g[u,v]) <> 0 then
    return false;
   fi;
  od;
 od;
 return true;
end:

`to_list/A2` := (f) -> [seq(seq(f[u,v],v=0..d-1-u),u=0..d-1)]:
`from_symbol/A2` := (f) -> table([seq(seq((u,v)=f[u,v],v=0..d-1-u),u=0..d-1)]);

`zero/A2`  := table([seq(seq((u,v)=0,v=0..d-1-u),u=0..d-1)]):
`one/A2`   := table([seq(seq((u,v)=1,v=0..d-1-u),u=0..d-1)]):
`delta/A2` := table([seq(seq((u,v)=`if`(u=0 and v = 0,1,0),v=0..d-1-u),u=0..d-1)]):

`plus/A2` := proc(f,g)
 table([seq(seq((u,v) = f[u,v]+g[u,v],v=0..d-1-u),u=0..d-1)]);
end:

`minus/A2` := proc(f,g)
 table([seq(seq((u,v) = f[u,v]-g[u,v],v=0..d-1-u),u=0..d-1)]);
end:

`dot/A2` := proc(f,g)
 table([seq(seq((u,v) = f[u,v]*g[u,v],v=0..d-1-u),u=0..d-1)]);
end:

`scalar_times/A2` := proc(c,f)
 table([seq(seq((u,v) = c*f[u,v],v=0..d-1-u),u=0..d-1)]);
end:

`mu/A2` := (u0,v0,u1,v1) -> q^(u0*v1+2*u1*v0);

`star/A2` := proc(f,g)
 local h,u,v,u0,u1,v0,v1;
 h := table();

 for u from 0 to d-1 do 
  for v from 0 to d-1-u do
   h[u,v] := 0;
  od;
 od:

 for u0 from 0 to d-1 do
  for u1 from 0 to d-1-u0 do
   for v0 from 0 to d-1-u0-u1 do
    for v1 from 0 to d-1-u0-u1-v0 do
     h[u0+u1,v0+v1] :=
      h[u0+u1,v0+v1] + 
       splitting_count(q)(u0,u1) * 
       splitting_count(q)(v0,v1) * 
       `mu/A2`(u0,v0,u1,v1) * 
       f[u0,v0] * g[u1,v1];
    od;
   od;
  od;
 od;

 return eval(h);
end:

######################################################################

`is_element/A3` := proc(f)
 local u,L;
 
 if not(type(f,table)) then
  return false;
 fi;

 L := [seq(seq(seq([u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)];

 if [indices(f)] <> L then
  return false;
 fi;

 return true;
end:

`is_equal/A3` := proc(f,g)
 local u,v,w;
 
 for u from 0 to d-1 do
  for v from 0 to d-1-u do
   for w from 0 to d-1-u-v do
    if simplify(f[u,v,w]-g[u,v,w]) <> 0 then
     return false;
    fi;
   od;
  od;
 od;
 return true;
end:

`to_list/A3` := (f) -> [seq(seq(seq(f[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]:
`from_symbol/A3` := (f) -> table([seq(seq(seq((u,v,w)=f[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]);

`zero/A3`  := table([seq(seq(seq((u,v,w)=0,w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]):
`one/A3`   := table([seq(seq(seq((u,v,w)=1,w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]):
`delta/A3` := table([seq(seq(seq((u,v,w)=`if`([u,v,w]=[0,0,0],1,0),w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]):

`plus/A3` := proc(f,g)
 table([seq(seq(seq((u,v,w) = f[u,v,w]+g[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]);
end:

`minus/A3` := proc(f,g)
 table([seq(seq(seq((u,v,w) = f[u,v,w]-g[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]);
end:

`dot/A3` := proc(f,g)
 table([seq(seq(seq((u,v,w) = f[u,v,w]*g[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]);
end:

`scalar_times/A3` := proc(c,f)
 table([seq(seq(seq((u,v,w) = c*f[u,v,w],w=0..d-1-u-v),v=0..d-1-u),u=0..d-1)]);
end:

`mu/A3` := (u0,v0,w0,u1,v1,w1) -> q^(u0*v1+u0*w1+v0*w1+2*u1*v0+2*u1*w0+2*v1*w0);

`star/A3` := proc(f,g)
 local h,u,v,w,u0,u1,v0,v1,w0,w1;
 h := table();

 for u from 0 to d-1 do 
  for v from 0 to d-1-u do
   for w from 0 to d-1-u-v do
    h[u,v,w] := 0;
   od;
  od;
 od:

 for u0 from 0 to d-1 do
  for u1 from 0 to d-1-u0 do
   for v0 from 0 to d-1-u0-u1 do
    for v1 from 0 to d-1-u0-u1-v0 do
     for w0 from 0 to d-1-u0-u1-v0-v1 do
      for w1 from 0 to d-1-u0-u1-v0-v1-w0 do
       h[u0+u1,v0+v1,w0+w1] :=
	h[u0+u1,v0+v1,w0+w1] + 
	 splitting_count(q)(u0,u1) * 
	 splitting_count(q)(v0,v1) * 
	 splitting_count(q)(w0,w1) * 
	 `mu/A3`(u0,v0,w0,u1,v1,w1) * 
	 f[u0,v0,w0] * g[u1,v1,w1];
      od;
     od;
    od;
   od;
  od;
 od;

 return eval(h);
end:

######################################################################

psi := proc(f)
 local h,u,v;

 h := table();

 for u from 0 to d-1 do 
  for v from 0 to d-1-u do
   h[u,v] := f[u+v];
  od;
 od:
 
 return eval(h);
end:

psi_L := proc(f)
 local h,u,v,w;

 h := table();

 for u from 0 to d-1 do 
  for v from 0 to d-1-u do
   for w from 0 to d-1-u-v do
    h[u,v,w] := f[u+v,w];
   od;
  od;
 od:
 
 return eval(h);
end:

psi_R := proc(f)
 local h,u,v,w;

 h := table();

 for u from 0 to d-1 do 
  for v from 0 to d-1-u do
   for w from 0 to d-1-u-v do
    h[u,v,w] := f[u,v+w];
   od;
  od;
 od:
 
 return eval(h);
end:

tensor11 := proc(f,g)
 table([seq(seq((u,v)=f[u]*g[v],v=0..d-1-u),u=0..d-1)]);
end: 

twisted_tensor11 := proc(f,g)
 table([seq(seq((u,v)=q^(u*v)*f[u]*g[v],v=0..d-1-u),u=0..d-1)]);
end: 

eta_L := (f) -> tensor11(`delta/A1`,f):

eta_R := (f) -> tensor11(f,`delta/A1`):

epsilon_L := proc(f)
 local h,u;

 h := table;

 for u from 0 to d-1 do
  h[u] := f[0,u];
 od;

 return eval(h):
end:

epsilon_R := proc(f)
 local h,u;

 h := table;

 for u from 0 to d-1 do
  h[u] := f[u,0];
 od;

 return eval(h):
end:

######################################################################

check_A1 := proc()
 local f,g,h,ff,gg,hh;

 ff := `from_symbol/A1`(f);
 gg := `from_symbol/A1`(g);
 hh := `from_symbol/A1`(h);
 
 printf("%a()\n",procname);

 _ASSERT(
  `is_equal/A1`(`star/A1`(`delta/A1`,ff),ff),"Left unit law"
 );

 _ASSERT(
  `is_equal/A1`(`star/A1`(ff,`delta/A1`),ff),"Right unit law"
 );

 _ASSERT(
  `is_equal/A1`(`star/A1`(ff,`star/A1`(gg,hh)),
                `star/A1`(`star/A1`(ff,gg),hh)),
  "Associativity law"
 );
end:

check_A2 := proc()
 local f,g,h,ff,gg,hh;

 ff := `from_symbol/A2`(f);
 gg := `from_symbol/A2`(g);
 hh := `from_symbol/A2`(h);
 
 printf("%a()\n",procname);

 _ASSERT(
  `is_equal/A2`(`star/A2`(`delta/A2`,ff),ff),"Left unit law"
 );

 _ASSERT(
  `is_equal/A2`(`star/A2`(ff,`delta/A2`),ff),"Right unit law"
 );

 _ASSERT(
  `is_equal/A2`(`star/A2`(ff,`star/A2`(gg,hh)),
                `star/A2`(`star/A2`(ff,gg),hh)),
  "Associativity law"
 );
end:

check_A3 := proc()
 local f,g,h,ff,gg,hh;

 ff := `from_symbol/A3`(f);
 gg := `from_symbol/A3`(g);
 hh := `from_symbol/A3`(h);
 
 printf("%a()\n",procname);

 _ASSERT(
  `is_equal/A3`(`star/A3`(`delta/A3`,ff),ff),"Left unit law"
 );

 _ASSERT(
  `is_equal/A3`(`star/A3`(ff,`delta/A3`),ff),"Right unit law"
 );

 _ASSERT(
  `is_equal/A3`(`star/A3`(ff,`star/A3`(gg,hh)),
                `star/A3`(`star/A3`(ff,gg),hh)),
  "Associativity law"
 );
end:

check_A_maps := proc()
 local f1,g1,h1,ff1,gg1,hh1,f2,g2,h2,ff2,gg2,hh2;

 ff1 := `from_symbol/A1`(f1);
 gg1 := `from_symbol/A1`(g1);
 hh1 := `from_symbol/A1`(h1);

 ff2 := `from_symbol/A2`(f2);
 gg2 := `from_symbol/A2`(g2);
 hh2 := `from_symbol/A2`(h2);

 _ASSERT(
  `is_equal/A2`(eta_L(`delta/A1`),`delta/A2`) and
  `is_equal/A2`(eta_L(`star/A1`(ff1,gg1)),`star/A2`(eta_L(ff1),eta_L(gg1))),
  "eta_L is a ring map"
 );

 _ASSERT(
  `is_equal/A2`(eta_R(`delta/A1`),`delta/A2`) and
  `is_equal/A2`(eta_R(`star/A1`(ff1,gg1)),`star/A2`(eta_R(ff1),eta_R(gg1))),
  "eta_R is a ring map"
 );

 _ASSERT(
  `is_equal/A2`(psi(`delta/A1`),`delta/A2`) and
  `is_equal/A2`(psi(`star/A1`(ff1,gg1)),`star/A2`(psi(ff1),psi(gg1))),
  "psi is a ring map"
 );

 _ASSERT(
  `is_equal/A1`(epsilon_L(`delta/A2`),`delta/A1`) and
  `is_equal/A1`(epsilon_L(`star/A2`(ff2,gg2)),`star/A1`(epsilon_L(ff2),epsilon_L(gg2))),
  "epsilon_L is a ring map"
 );

 _ASSERT(
  `is_equal/A1`(epsilon_R(`delta/A2`),`delta/A1`) and
  `is_equal/A1`(epsilon_R(`star/A2`(ff2,gg2)),`star/A1`(epsilon_R(ff2),epsilon_R(gg2))),
  "epsilon_R is a ring map"
 );

 _ASSERT(
  `is_equal/A1`(epsilon_L(psi(ff1)),ff1),
  "epsilon_L o psi = 1"
 );

 _ASSERT(
  `is_equal/A1`(epsilon_R(psi(ff1)),ff1),
  "epsilon_R o psi = 1"
 );

 _ASSERT(
  `is_equal/A2`(`star/A2`(eta_R(ff1),eta_L(gg1)),twisted_tensor11(ff1,gg1)),
  "eta_R * eta_L"
 );
end;

