# Given elements a[i] in A we have elements 1 - a[i] in the group ring.
# The tensor product of these is represented by `bar/BA`(a[1],...,a[n])

`bar/BA` := proc ()
 local i;
 for i to nargs do
  if args[i] = 1 then return 0 fi;
 od;
 return '`bar/BA`'(args);
end:

# The standard differential in the bar complex is `d/BA`

`d/BA` := (u) -> sort(expand(eval(subs(`bar/BA`=`d_bar/BA`,u))));

`d_bar/BA` := proc()
 local n,i,q;
 n := nargs;
 if n = 0 then
  return 0;
 else 
  return -`bar/BA`(args[2..n]) + 
         (-1)^(n+1)*`bar/BA`(args[1..n-1]) +
         add((-1)^(i+1)*`bar/BA`(args[1..i-1],args[i]*args[i+1],args[i+2..n]),
             i=1..n-1);
 fi;
end:

# The shuffle product in the bar complex is `mu/BA`

`mu/BA` := proc()
 apply_linear_assoc(`mu_aux0/BA`,`bar/BA`())(args);
end:

`mu_aux0/BA` := proc(u,v)
 local r,s,i,ii,j;
 r := nops(u);
 s := nops(v);
 if r = 0 then return v; fi;
 if s = 0 then return u; fi;
 ii := [seq([i],i=1..r+s)];
 for i from 2 to r do
  ii := map(`ext/BA`,ii,r+s);
 od;
 return add(`mu_aux1/BA`(u,v,ii[j]),j=1..nops(ii));
end:

`ext/BA` := proc (i, r)
 local j;
 seq([op(i), j], j = i[nops(i)]+1 .. r);
end:

`mu_aux1/BA` := proc (u, v, i)
 local r,s,q,j,k,m;
 r := nops(u);
 s := nops(v);
 q := [EMPTY$r+s];
 for j to r do
  q[i[j]] := op(j, u)
 od;
 k := 1;
 for j to r+s do
  if q[j] = EMPTY then
   q[j] := op(k, v);
   k := k+1;
  fi;
 od;
 m := `+`(op(i))-(1/2)*r*(r+1);
 return (-1)^m*`bar/BA`(op(q))
end:

`mu_bar/BA` := proc()
 `mu/BA`(op(map(`bar/BA`,[args])));
end:

######################################################################
# The element u = `tau/BA`(n,a) has du = n[a] - [a^n].
# Thus, if a^n = 1 then u is a 2-cycle modulo n.

`tau/BA` := proc(n,a)
 local k;
 add(-`bar/BA`(a^k,a),k=0..n-1);
end:

`zeta/BA` := proc(n,m,a)
 local i,j;
 - add(add(`bar/BA`(a^(m*i),a^j,a),j=0..m-1),i=0..n-1);
end:

# The element `sigma/BA`(n,a,b) is a chain of dimension 3.
# It is symmetric in a and b, and is a cycle if a^n = b^n = 1.

`sigma/BA` := proc(n,a,b)
 `mu/BA`(`tau/BA`(n, a), `bar/BA`(b)) +
 `mu/BA`(`tau/BA`(n, b), `bar/BA`(a))
end:

# The element u = `gamma/BA`(n,a) is a chain of dimension 2n+1.
# It is a cycle if a^n = 1.

`gamma/BA` := proc(n,k,a)
 local u,v,i;
 u := `bar/BA`(a);
 v := `tau/BA`(n,a);
 for i from 1 to k do
  u := `mu/BA`(u,v);
 od;
 u := expand(u/k!);
 return u;
end:

`rho/BA` := proc(n,a,b)
 `tau/BA`(n,a) +
 `tau/BA`(n,b) -
 `tau/BA`(n,a*b) +
 n*`bar/BA`(a, b);
end:

`omega/BA` := proc (n,a,b)
 local i,j;
 -add(add(`bar/BA`(a^i*b^j,b,a), j = i .. n-1), i = 0 .. n-1) +
  add(add(`bar/BA`(a^i*b^j,a,b), j = i+1 .. n-1), i = 0 .. n-2);
end:

######################################################################
# We now introduce the standard DGA for H_*(BZ/n).

# The k'th chain group is freely generated over Z[Z/n] by
# `e/EC`(n,k,0).  The orbit of this consists of elements `e/EC`(n,k,i).

`e/EC` := proc(n::posint,k::nonnegint,i::nonnegint)
 '`e/EC`'(n,k,modp(i,n));
end:

`de/EC` := proc(n::posint,k::nonnegint,i::nonnegint)
 local j;
 if k = 0 then
  return 0;
 elif modp(k,2) = 0 then
  return(add(`e/EC`(n,k-1,j),j=0..n-1));
 else
  return `e/EC`(n,k-1,modp(i+1,n)) - `e/EC`(n,k-1,i);
 fi;
end:

`d/EC` := (u) -> eval(subs(`e/EC` = `de/EC`,u));

`mu/EC` := proc(a,b)
 local xx,ca,cb,pa,pb,na,nb,ka,kb,la,lb,ia,ib;
 if nargs > 2 then
  return `mu/EC`(`mu/EC`(a,b),args[3..-1]);
 fi;
 if type(a,numeric) or type(b,numeric) then
  return expand(a*b);
 elif type(a,`+`) then
  return map(`mu/EC`,a,b);
 elif type(b,`+`) then
  return map2(`mu/EC`,a,b);
 fi;
 if type(a,`*`) then 
  xx := selectremove(type,a,numeric);
  ca := xx[1];
  pa := xx[2];
 else
  ca := 1;
  pa := a;
 fi;
 if type(b,`*`) then 
  xx := selectremove(type,b,numeric);
  cb := xx[1];
  pb := xx[2];
 else
  cb := 1;
  pb := b;
 fi;
 if type(pa,specfunc(anything,`e/EC`)) and
    type(pb,specfunc(anything,`e/EC`)) then
  na,ka,ia := op(pa);
  nb,kb,ib := op(pb);
  if nb <> na then return FAIL; fi;
  if modp(ka,2) = 1 and modp(kb,2) = 1 then
   return 0;
  fi;
  la := floor(ka/2);
  lb := floor(kb/2);
  return ca * cb * binomial(la+lb,la) * `e/EC`(na,ka+kb,modp(ia+ib,na));
 else
  return('`mu/EC`'(args))
 fi;
end:

##################################################

`e/BC` := proc(n::posint,k::nonnegint)
 '`e/BC`'(n,k);
end:

`de/BC` := proc(n::posint,k::nonnegint)
 if k = 0 or modp(k,2) = 1 then
  return 0;
 else
  return n * `e/BC`(n,k-1);
 fi;
end:

`d/BC` := (u) -> eval(subs(`e/BC` = `de/BC`,u));

`mu/BC` := proc(a,b)
 local xx,ca,cb,pa,pb,na,nb,ka,kb,la,lb,ia,ib;
 if nargs > 2 then
  return `mu/BC`(`mu/BA`(a,b),args[3..-1]);
 fi;
 if type(a,numeric) or type(b,numeric) then
  return expand(a*b);
 elif type(a,`+`) then
  return map(`mu/BC`,a,b);
 elif type(b,`+`) then
  return map2(`mu/BC`,a,b);
 fi;
 if type(a,`*`) then 
  xx := selectremove(type,a,numeric);
  ca := xx[1];
  pa := xx[2];
 else
  ca := 1;
  pa := a;
 fi;
 if type(b,`*`) then 
  xx := selectremove(type,b,numeric);
  cb := xx[1];
  pb := xx[2];
 else
  cb := 1;
  pb := b;
 fi;
 if type(pa,specfunc(anything,`e/BC`)) and
    type(pb,specfunc(anything,`e/BC`)) then
  na,ka := op(pa);
  nb,kb := op(pb);
  if nb <> na then return FAIL; fi;
  if modp(ka,2) = 1 and modp(kb,2) = 1 then
   return 0;
  fi;
  la := floor(ka/2);
  lb := floor(kb/2);
  return ca * cb * binomial(la+lb,la) * `e/BC`(na,ka+kb);
 else
  return('`mu/BC`'(args))
 fi;
end:

`e/BC/BA` := proc(n::posint,k::nonnegint)
 option remember;

 if k = 0 then
  return `bar/BA`();
 elif k = 1 then
  return `bar/BA`(a);
 else
  return expand(`mu/BA`(`tau/BA`(n,a),`e/BC/BA`(n,k-2))/floor(k/2));
 fi;
end:

`phi/BC/BA` := proc(u)
 eval(subs(`e/BC` = `e/BC/BA`,u));
end:

######################################################################

check_abelian_group_homology := proc()
 local i,j,k,n,m,a,b,c,t,u,v,w,T,ok,err,exp_rel,diff_rel;

 ok := true;
 for i from 0 to 4 do
  for j from 0 to 4 do 
   u := `bar/BA`(seq(a[m],m=1..i)); 
   v := `bar/BA`(seq(a[m],m=i+1..i+j));
   err := `mu/BA`(u,v) - (-1)^(i*j) * `mu/BA`(v,u);
   if err <> 0 then
    ok := false;
    break;
   fi;
  od:
  if not(ok) then break; fi;
 od:

 _ASSERT(ok,"`mu/BA` is graded-commutative");

 ok := true;
 for i from 0 to 4 do
  for j from 0 to 4 do 
   for k from 0 to 4 do 
    u := `bar/BA`(seq(a[m],m=1..i)); 
    v := `bar/BA`(seq(a[m],m=i+1..i+j));
    w := `bar/BA`(seq(a[m],m=i+j+1..i+j+k));
    err := `mu/BA`(`mu/BA`(u,v),w) - `mu/BA`(u,`mu/BA`(v,w));
    if err <> 0 then
     ok := false;
     break;
    fi;
   od:
   if not(ok) then break; fi;
  od:
  if not(ok) then break; fi;
 od:

 _ASSERT(ok,"`mu/BA` is associative");

 n := 5;
 err := `d/BA`(`tau/BA`(n,a)) - n * `bar/BA`(a);
 exp_rel := `bar/BA`(a^n);
 err := err + exp_rel;
 
 _ASSERT(err = 0,"d(tau_n(a))");

 err := 
  `d/BA`(`mu/BA`(`tau/BA`(n,a),`bar/BA`(b))) - n * `mu_bar/BA`(a,b);
 exp_rel := `mu_bar/BA`(a^n,b); 
 err := err + exp_rel;

 _ASSERT(err = 0,"d(tau_n(a) b)");

 _ASSERT(
  {seq(seq(
   `tau/BA`(i*j,a) - `tau/BA`(i,a^j) - i * `tau/BA`(j,a) - `d/BA`(`zeta/BA`(i,j,a)),
  j=1..4),i=1..4)} = {0},
  "tau_{ij}(a)"
 );

 err := `d/BA`(`sigma/BA`(n,a,b));
 exp_rel := `mu_bar/BA`(a^n,b) - `mu_bar/BA`(a,b^n);
 err := err + exp_rel;

 _ASSERT(err = 0,"d(sigma_n(a,b))");

 _ASSERT(`sigma/BA`(n,a,b) = `sigma/BA`(n,b,a),"sigma_n is symmetric");
 
 err :=
  `sigma/BA`(n,a,b*c) - `sigma/BA`(n,a,b) - `sigma/BA`(n,a,c) +
    `mu/BA`(`bar/BA`(a),`rho/BA`(n,b,c));
 diff_rel := - `mu/BA`(`tau/BA`(n,a),`bar/BA`(b,c));
 exp_rel  := - `mu/BA`(`bar/BA`(a^n),`bar/BA`(b,c));
 err := err + `d/BA`(diff_rel) + exp_rel;

 _ASSERT(err = 0,"First formula for sigma_n(a,bc)");

 err := 
  `sigma/BA`(n,a,b*c)-`sigma/BA`(n,a,b)-`sigma/BA`(n,a,c)+
   binomial(n+1,2)*`mu_bar/BA`(a,b,c);
   
 diff_rel := -(`mu/BA`(`bar/BA`(a),`omega/BA`(n,b,c))+
  	       `mu/BA`(`tau/BA`(n,a),`bar/BA`(b,c)));
 exp_rel := 
  - `mu/BA`(`bar/BA`(a^n),`bar/BA`(b,c)) - 
  add(`bar/BA`(a,b^i,b)-`bar/BA`(a,b^i*c^n,b),i=0..n-1)- 
  add(`bar/BA`(b^i,b,a)-`bar/BA`(b^i*c^n,b,a),i=0..n-1)+
  add(`bar/BA`(b^i,a,b)-`bar/BA`(b^i*c^n,a,b),i=0..n-1);

 err := err + `d/BA`(diff_rel) + exp_rel;

 _ASSERT(err = 0,"Second formula for sigma_n(a,bc)");

 for k from 1 to 5 do
  err := `d/BA`(`gamma/BA`(n,k,a));
  T := [[]]:
  for i from 1 to k-1 do
   T := [seq(seq([op(t),a,a^j],j=1..n-1),t in T)]:
  od:
  exp_rel := (-1)^k*add(`mu/BA`(`bar/BA`(op(t),a),`bar/BA`(a^n)),t in T);
  err := err + exp_rel;
  _ASSERT(err = 0,sprintf("d(gamma_{n,%d}(u))",k));
 od:

 _ASSERT(simplify(`sigma/BA`(n,a,a) - 2 * `gamma/BA`(n,1,a)) = 0,
         "sigma_n(a,a) = 2 gamma_{n,1}(a)");
	 
 err := 
  `gamma/BA`(n,1,a*b) - `gamma/BA`(n,1,a) - `gamma/BA`(n,1,b) -
    `sigma/BA`(n,a,b);

 diff_rel :=
  n*`bar/BA`(a,b,a,b) -
  `mu/BA`(`bar/BA`(a,b),`tau/BA`(n,a*b)) +
  `mu/BA`(`omega/BA`(n,a,b),`bar/BA`(a)+`bar/BA`(b));
  
 exp_rel := 
  add(`bar/BA`(a^i,b,a) - `bar/BA`(a^i*b^5,b,a),i=0..n-1) -
  add(`bar/BA`(a^i,a,b) - `bar/BA`(a^i*b^5,a,b),i=0..n-1) -
  add(`bar/BA`(b,a^i,a) - `bar/BA`(b,a^i*b^5,a),i=0..n-1) -
  add(`bar/BA`(a,a^i,a) - `bar/BA`(a,a^i*b^5,a),i=0..n-1) -
 `mu/BA`(`bar/BA`(a^n*b^n),`bar/BA`(a,b));

 err := err + `d/BA`(diff_rel) + exp_rel;

 _ASSERT(err = 0,"gamma_{n,1}(ab)");
end:

######################################################################

check_cyclic_group_homology := proc()
 local n,ok,u,v,w,ku,kv,kw,err;
 
 n := 5;

 ok := true;
 for ku from 0 to 4 do
  for kv from 0 to 4 do
   u := `e/BC`(n,ku);
   v := `e/BC`(n,kv);
   err := `mu/BC`(u,v) - (-1)^(ku*kv) * `mu/BC`(v,u);
   if err <> 0 then
    ok := false;
    break;
   fi;
  od:
  if not(ok) then break; fi;
 od:

 _ASSERT(ok,"`mu_BC` is graded-commutative");

 ok := true;
 for ku from 0 to 4 do
  for kv from 0 to 4 do
   for kw from 0 to 4 do
    u := `e/BC`(n,ku);
    v := `e/BC`(n,kv);
    w := `e/BC`(n,kw);
    err := `mu/BC`(`mu/BC`(u,v),w) - `mu/BC`(u,`mu/BC`(v,w));
    if err <> 0 then
     ok := false;
     break;
    fi;
   od:
   if not(ok) then break; fi;
  od:
 od:
 
 _ASSERT(ok,"`mu_BC` is associative",[u,v,w,err]);

 ok := true;
 for ku from 0 to 4 do
  for kv from 0 to 4 do
   u := `e/BC`(n,ku);
   v := `e/BC`(n,kv);
   err := `d/BC`(`mu/BC`(u,v)) - `mu/BC`(`d/BC`(u),v) - (-1)^ku * `mu/BC`(u,`d/BC`(v));
   if err <> 0 then
    ok := false;
    break;
   fi;
  od:
  if not(ok) then break; fi;
 od:

 _ASSERT(ok,"Leibniz rule for BC");
end:
