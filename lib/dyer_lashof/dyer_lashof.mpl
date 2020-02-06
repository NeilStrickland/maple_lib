p := 5;

# b(i) is the image in H_{2i}(QS^0) of the standard generator of H_{2i}(BC_p)
# This is zero unless i is divisible by p-1.  An expression like b(8,4,6)
# represents the circle product of b(8), b(4) and b(6).

b := proc()
 if map(mods,{0,args},p-1) <> {0} or min(0,args) < 0 then
  return(0);
 fi;
 'b'(op(sort([args]))); 
end:

# Signature of permutations of {1,...,n}, represented as lists of values.
# Sends non-permutations to zero.
signature := proc(s)
 local i,j,x;
 x := 1; 
 for i from 1 to nops(s)-1 do
  for j from i+1 to nops(s) do
   if op(i,s) > op(j,s) then
    x := -x;
   elif op(i,s) = op(j,s) then
    return(0);
   fi;
  od;
 od;
 x;
end:

# a(i) is the image in H_{2i+1}(QS^0) of the standard generator of H_{2i+1}(BC_p)
# This is zero unless i+1 is divisible by p-1.  An expression like a(11,3,7)
# represents the circle product of a(11), a(3) and a(7).
a := proc()
 if map(modp,{-1,args},p-1) <> {p-2} or min(0,args) < 0 then
  return(0);
 fi;
 signature([args]) * 'a'(op(sort([args]))); 
end:


# The elements b(i) satisfy \sum b(i,j) s^i t^j=\sum b(i,j) s^i (s+t)^j.  
# By expanding this out we see that b_rel(i,j) = 0 for all i and j,
# where b_rel(i, j) is as defined below.

b_rel := proc(i,j)
 add(mods(binomial(i+j-u,j),p) * b(u,i+j-u),u=0..i-1);
end:

b_rels := proc(d) [seq(b_rel(i,d-i),i=0..d)]; end:

# The elements a(i) satisfy \sum a(i,j) s^i t^j=\sum a(i,j) s^i (s+t)^j.  
# By expanding this out we see that a_rel(i,j) = 0 for all i and j,
# where a_rel(i, j) is as defined below.

a_rel := proc(i,j)
 add(mods(binomial(i+j-u,j),p) * a(u,i+j-u),u=0..i-1);
end:

a_rels := proc(d) [seq(a_rel(i,d-i),i=0..d)]; end:


# Degree function for expressions in a's, b's, P's and Q's.
# Should be refactored to use apply_deg
# Not sure what the P's and Q's are
deg := proc(x) 
 local d,n;
 if type(x,`+`) then
  d := map(deg,{op(x)});
  if nops(d) = 1 then
   return(op(1,d));
  else
   error("inhomogeneous sum");
  fi;
 elif type(x,`*`) then
  return(`+`(op(map(deg,[op(x)]))));
 elif type(x,function) and op(0,x) = o then
  return(`+`(op(map(deg,[op(x)]))));
 elif type(x,integer) then
  return(0);
 elif type(x,function) and op(0,x) = a then
  return(`+`(op(map(i->2*i+1,[op(x)]))));
 elif type(x,function) and op(0,x) = b then
  return(`+`(op(map(i->2*i,[op(x)]))));
 elif type(x,function) and op(0,x) = P then
  n := nops(x)/2;
  return( -2*(p-1)*add(op(2*i,x),i=1..n) - add(op(2*i-1,x),i=1..n));
 elif type(x,function) and op(0,x) = Q then
  n := nops(x)/2;
  return( 2*(p-1)*add(op(2*i,x),i=1..n) - add(op(2*i-1,x),i=1..n));
 fi;
end:

# Circle product.  Shoud be refactored to use apply_*
o := proc()
 local xx;
 xx := map(mods,[args],p);
 if member(0,xx) then
  return(0);
 else
  return('o'(op(xx)));
 fi; 
end:

# Bockstein operation.  Recognises star and circle products, a's, b's and Q's
beta := proc(x) 
 local xx,n,s,y,i,j;
 if type(x,`+`) then
  return(map(beta,x));
 elif type(x,`*`) then
  xx := [op(x)];
  n := nops(xx);
  s := 1;
  y := 0;
  for i from 1 to n do
   y := y + s * mul(xx[j],j=1..(i-1)) * beta(xx[i]) * mul(xx[j],j=i+1..n);
   s := s * (-1)^deg(xx[i]);
  od;
  return(mods(expand(y),p));
 elif type(x,function) and op(0,x) = o then
  xx := [op(x)];
  n := nops(xx);
  s := 1;
  y := 0;
  for i from 1 to n do
   y := y + s * o(seq(xx[j],j=1..(i-1)),beta(xx[i]),seq(xx[j],j=i+1..n));
   s := s * (-1)^deg(xx[i]);
  od;
  return(mods(expand(y),p));
 elif type(x,integer) then
  return(0);
 elif type(x,function) and op(0,x) = a then
  return(0);
 elif type(x,function) and op(0,x) = b then
  xx := [op(x)];
  n := nops(xx);
  y := 0;
  for i from 1 to n do 
   if xx[i] > 0 then
    y := y + o(a(xx[i]-1),b(seq(xx[j],j=1..i-1),seq(xx[j],j=i+1..n)));
   fi;
  od;
  return(mods(expand(y),p));
 elif type(x,function) and op(0,x) = Q then
  if nops(x) = 0 or op(1,x) = 1 then return(0); fi;
  return(Q(1,op(2..-1,x))); 
 else 
  return('beta'(x));
 fi; 
end:

# Dyer-Lashof operation.  Only knows linearity and the Cartan rule
QQ := proc(i,x)
 local y,z;
 if type(x,`+`) then
  return(map2(QQ,i,x));
 elif type(x,`*`) then
  y := op(1,x);
  z := `*`(op(2..-1,x));
  if type(y,integer) then 
   return(mods(expand(y*QQ(i,z)),p));
  else 
   return(mods(expand(add(QQ(j,y)*QQ(i-j,z),j=0..i)),p));
  fi;
 elif type(x,integer) then
  if i = 0 then
   return(x);
  else
   return(0);
  fi;
 else
  return('QQ'(i,x));
 fi;
end:

# Steenrod operation.  Knows the Cartan rule for star and circle products,
# and behaviour on a's, b's and Q's.
PP := proc(i,x)
 local y,z,j,s;
 if i<0 then 
  return(0);
 elif i=0 then
  return(x);
 elif type(x,`+`) then
  return(map2(PP,i,x));
 elif type(x,`*`) then
  y := op(1,x);
  z := `*`(op(2..-1,x));
  if type(y,integer) then 
   return(mods(expand(y*PP(i,z)),p));
  else 
   return(mods(expand(add(PP(j,y)*PP(i-j,z),j=0..i)),p));
  fi;
 elif type(x,function) and op(0,x) = o then
  y := op(1,x);
  z := o(op(2..-1,x));
  if type(y,integer) then 
   return(mods(expand(y * PP(i,z)),p));
  else 
   return(mods(expand(add(o(PP(j,y),PP(i-j,z)),j=0..i)),p));
  fi;
 elif type(x,integer) then
  if i = 0 then
   return(x);
  else
   return(0);
  fi;
 elif type(x,function) and op(0,x) = b then
  j := op(1,x);
  if nops(x) = 1 then
   return(mods(binomial(j-(p-1)*i,i),p)*b(j-(p-1)*i));
  else 
   z := b(op(2..-1,x));
   return(mods(expand(add(binomial(j-(p-1)*k,k)*o(b(j-(p-1)*k),PP(i-k,z)),k=0..j/(p-1))),p));
  fi;
 elif type(x,function) and op(0,x) = a then
  j := op(1,x);
  if nops(x) = 1 then
   return(mods(binomial(j-(p-1)*i,i),p)*a(j-(p-1)*i));
  else
   z := a(op(2..-1,x));
   return(mods(expand(add(binomial(j-(p-1)*k,k)*o(a(j-(p-1)*k),PP(i-k,z)),k=0..j/(p-1))),p));
  fi;
 elif type(x,function) and op(0,x) = Q then
  if nops(x) = 0 then
   if i=0 then return(x) else return(0); fi;
  fi;
  s := op(2,x);
  y := Q(op(3..-1,x));
  if op(1,x) = 0 then
   return(add((-1)^(i+k)*binomial((s-i)*(p-1),i-p*k)*oQ(Q(0,s-i+k),PP(k,y)),k=0..i/p));
  else
   return(zap(
    add((-1)^(i+k)*binomial((s-i)*(p-1)-1,i-p*k)*oQ(Q(1,s-i+k),PP(k,y)),k=0..i/p) + 
    add((-1)^(i+k)*binomial((s-i)*(p-1)-1,i-p*k-1)*oQ(Q(0,s-i+k),PP(k,beta(y))),k=0..i/p)
   ));
  fi;
 else
  return('PP'(i,x));
 fi;
end:

# Length function for Steenrod or Dyer-Lashof words.
len := proc(x) 
 if type(x,function) and (op(0,x) = P or op(0,x) = Q) then
  return(nops(x)/2);
 else
  return('len'(x));
 fi; 
end:

# Excess for Dyer-Lashof words
excess := proc(x)
 local n;
 if type(x,function) and op(0,x) = Q then
  n := nops(x)/2;
  if n = 0 then return(0); fi; 
  return(2*op(2,x) - op(1,x) - add(2*(p-1)*op(2*i,x)-op(2*i-1,x),i=2..n));
 else
  return('excess'(x));
 fi;
end:

# Admissibility criterion for Dyer-Lashof words
is_admissible := proc(x)
 local i,n;
 if type(x,function) and op(0,x) = Q then
  n := nops(x)/2;
  if n = 0 then
   return(true);
  fi;
  if op(2,x) < op(1,x) then
   return(false);
  fi;
  for i from 2 to n do
   if p*op(2*i,x) - op(2*i-1,x) < op(2*i-2,x) then
    return(false);
   fi;
  od;
  return(true);
 else
  return('is_admissible'(x));
 fi;
end:

Q_adem := proc() 
 local i,j,u,ep,r,dl,s,v;
 if nargs = 0 then
  return(Q());
 fi;
 if args[2] < args[1] then
  # (we must have args[1] = 1, args[2] = 0)
  if nargs = 2 then
#   error("naked beta");
   return(Q(1,0));
  fi;
  if args[3] = 1 then
   return(0);
  else
   return(Q(1,args[4..-1]));
  fi;
 fi;
 for i from 2 to nargs/2 do
  u  := args[1..2*i-4];
  ep := args[2*i-3];
  r  := args[2*i-2];
  dl := args[2*i-1];
  s  := args[2*i  ];
  v  := args[2*i+1..-1];
  if r > p*s-dl then
   if dl = 0 then 
    return(
     mods(add(
      (-1)^(r+j)*binomial((p-1)*(j-s)-1,p*j-r)*
       Q(u,ep,r+s-j,0,j,v),
      j=ceil(r/p)..(r-(p-1)*s-1)
     ),p)
    );
   else
    if ep = 0 then
     return(mods(add(
      (-1)^(r+j)*binomial((p-1)*(j-s),p*j-r)*
       Q(u,1,r+s-j,0,j,v),
      j=ceil(r/p)..(r-(p-1)*s)
     ),p) - 
     mods(add(
      (-1)^(r+j)*binomial((p-1)*(j-s)-1,p*j-r-1)*
       Q(u,0,r+s-j,1,j,v),
       j = ceil((r+1)/p)..(r-(p-1)*s)
     ),p));
    else 
     return(mods(add(
      (-1)^(r+j+1)*binomial((p-1)*(j-s)-1,p*j-r-1)*
       Q(u,1,r+s-j,1,j,v),
       j = ceil((r+1)/p)..(r-(p-1)*s)
     ),p));
    fi;
   fi;
  fi;
 od;
 return(Q(args));
end:

Q_exc0 := proc()
 if excess(Q(args)) < 0 then
  return(0);
 else
  return(Q(args));
 fi;
end:

Q_comp := proc(a,b) 
 local aa,bb,n,m,i,d;
 aa := a;
 bb := b;
 if type(aa,`*`) then
  aa := select(type,a,specfunc(integer,Q));
 fi;
 if type(bb,`*`) then
  bb := select(type,b,specfunc(integer,Q));
 fi;
 if not(type([aa,bb],[specfunc(integer,Q)$2])) then
  error("invalid arguments");
 fi;
 n := nops(aa)/2;
 m := nops(bb)/2;
 for i from 1 to min(n,m) do
  d := 2*op(2*i,aa) - op(2*i-1,aa) - 2*op(2*i,bb) + op(2*i-1,bb);
  if d < 0 then
   return(true);
  elif d > 0 then
   return(false);
  fi;
 od; 
 if n<m then return(true); fi;
 return(false);
end:

Q_terms := proc(x) 
 if type(x,specfunc(integer,Q)) then
  return([x]);
 elif type(x,`*`) then
  return(select(type,[op(x)],specfunc(integer,Q)));
 elif type(x,`+`) then
  return(map(op,map(Q_terms,[op(x)])));
 else
  return([]);
 fi;
end:

Q_bot := proc(x)
 local t;
 t := sort(Q_terms(x),Q_comp);
 if t = [] then
  return(0);
 else
  return(t[1]);
 fi;
end:

Q_top := proc(x)
 local t;
 t := sort(Q_terms(x),Q_comp);
 if t = [] then
  return(0);
 else
  return(t[nops(t)]);
 fi;
end:

oQ := proc(a,b)
 local n,aa,bb;
 if type(a,`+`) then
  return(map(oQ,a,b));
 elif type(b,`+`) then
  return(map2(oQ,a,b));
 fi;
 if type(a,`*`) then
  n,aa := selectremove(type,a,integer);
  if n<>1 then
   return(expand(n*oQ(aa,b)));
  fi;
 fi;
 if type(b,`*`) then
  n,bb := selectremove(type,b,integer);
  if n<> 1 then
   return(expand(n*oQ(a,bb)));
  fi;
 fi;
 if type(a,integer) or type(b,integer) then
  return(expand(a*b)); 
 fi;
 if type(a,specfunc(integer,Q)) and type(b,specfunc(integer,Q)) then
  return(Q(op(a),op(b)));
 fi;
end:

zap := proc(x) mods(eval(subs(Q=Q_exc0,eval(subs(Q = Q_adem,x)))),p); end:

