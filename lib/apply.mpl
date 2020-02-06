apply_linear := (f) -> proc(u)
 local c,v;
 
 if u = 0 then
  return 0;
 elif type(u,`+`) then
  return map(apply_linear(f),u);
 elif type(u,`*`) then
  c,v := selectremove(type,u,rational);
  return c * f(v);
 elif type(u,rational) then
  return u * f(1);
 else
  return f(u);
 fi;
end:

apply_linear_mod := (f,m::posint) -> proc(u)
 local c,v;
 
 if u = 0 then
  return 0;
 elif type(u,`+`) then
  return modp(map(apply_linear(f),u),m);
 elif type(u,`*`) then
  c,v := selectremove(type,u,integer);
  c := modp(c,m);
  if c = 0 then
   return 0;
  else 
   return modp(expand(c * f(v)),m);
  fi;
 elif type(u,integer) then
  return modp(u * f(1),m);
 else
  return f(u);
 fi;
end:

apply_list_linear := (f) -> proc(u)
 local c,v;
 
 if u = 0 then
  return 0;
 elif type(u,`+`) or type(u,list) or type(u,set) then
  return map(apply_list_linear(f),u);
 elif type(u,`*`) then
  c,v := selectremove(type,u,rational);
  return c * f(v);
 elif type(u,rational) then
  return u * f(1);
 else
  return f(u);
 fi;
end:

apply_list_linear_mod := (f,m::posint) -> proc(u)
 local c,v;
 
 if u = 0 then
  return 0;
 elif type(u,`+`) or type(u,list) or type(u,set) then
  return modp(map(apply_list_linear(f),u),m);
 elif type(u,`*`) then
  c,v := selectremove(type,u,integer);
  c := modp(c,m);
  if c = 0 then
   return 0;
  else 
   return modp(expand(c * f(v)),m);
  fi;
 elif type(u,rational) then
  return modp(u * f(1),m);
 else
  return f(u);
 fi;
end:

apply_bilinear := (f) -> proc(u,v)
 local cu,xu,cv,xv;

 if u = 0 or v = 0 then
  return 0; 
 elif type(u,`+`) then
  return map(apply_bilinear(f),u,v);
 elif type(v,`+`) then
  return map2(apply_bilinear(f),u,v);
 fi;

 if type(u,`*`) then
  cu,xu := selectremove(type,u,rational);
 else
  cu,xu := 1,u;
 fi;
 
 if type(v,`*`) then
  cv,xv := selectremove(type,v,rational);
 else
  cv,xv := 1,v;
 fi;

 return cu * cv * f(xu,xv);
end:

apply_bilinear_mod := (f,m::posint) -> proc(u,v)
 local cu,xu,cv,xv,c;

 if u = 0 or v = 0 then
  return 0; 
 elif type(u,`+`) then
  return modp(map(apply_bilinear(f),u,v),m);
 elif type(v,`+`) then
  return modp(map2(apply_bilinear(f),u,v),m);
 fi;

 if type(u,`*`) then
  cu,xu := selectremove(type,u,integer);
 else
  cu,xu := 1,u;
 fi;
 
 if type(v,`*`) then
  cv,xv := selectremove(type,v,integer);
 else
  cv,xv := 1,v;
 fi;

 c := modp(cu * cv,m);
 if c = 0 then
  return 0;
 else
  return modp(expand(c * f(xu,xv)),m);
 fi;
end:

apply_assoc := (f,e) -> proc()
 if nargs = 0 then
  return e;
 elif nargs = 1 then
  return args[1];
 elif args = 2 then
  return f(args[1],args[2]);
 else
  return f(args[1],apply_assoc(f,e)(args[2..-1]));
 fi;
end:

apply_linear_assoc_mod := (f,e,m::posint) -> proc()
 if nargs = 0 then
  return e;
 elif nargs = 1 then
  return args[1];
 elif args = 2 then
  return apply_bilinear_mod(f,m)(args[1],args[2]);
 else
  return apply_bilinear_mod(f,m)(args[1],apply_linear_assoc_mod(f,e,m)(args[2..-1]));
 fi;
end:

apply_deg := proc(f,deg_type := rational)
 return 
  proc(u)
   local c,v,d,e,i,n;

   if u = 0 then
    return 0;
   elif type(u,`+`) then
    d := map(apply_deg(f),{op(u)});
    if nops(d) = 1 then
     return d[1];
    else
     return FAIL;
    fi;
   elif type(u,`*`) then
    d := map(apply_deg(f),[op(u)]);
    if type(d[1],deg_type) then
     return `+`(op(d));
    elif type(d[1],list) then
     e := d[1];
     for i from 2 to nops(d) do e := e +~ d[i]; od;
     return e;
    else
     return FAIL;
    fi;
   elif type(u,`^`) and type(op(2,u),deg_type) then
    d := apply_deg(f)(op(1,u));
    n := op(2,u);
    if type(d,deg_type) then
     return n*d;
    elif type(d,list) then
     return n *~ d;
    else
     return FAIL;
    fi;
   else
    return f(u);
   fi;
  end:
end:

apply_max_deg := (f) -> proc(u)
 local c,v,d,e,i,n;
 
 if u = 0 then
  return 0;
 elif type(u,`+`) then
  return max(op(map(apply_max_deg(f),{op(u)})));
 elif type(u,`*`) then
  d := map(apply_max_deg(f),[op(u)]);
  if type(d[1],rational) then
   return `+`(op(d));
  elif type(d[1],list) then
   e := d[1];
   for i from 2 to nops(d) do e := e +~ d[i]; od;
   return e;
  else
   return FAIL;
  fi;
 elif type(u,`^`) and type(op(2,u),rational) then
  d := apply_max_deg(f)(op(1,u));
  n := op(2,u);
  if type(d,rational) then
   return n*d;
  elif type(d,list) then
   return n *~ d;
  else
   return FAIL;
  fi;
 else
  return f(u);
 fi;
end:

apply_leibniz := (f) -> proc(u)
 local n,v,uu;
 
 if type(u,`+`) or type(u,list) or type(u,set) then
  return map(apply_leibniz(f),u);
 elif type(u,`*`) then
  uu := [op(u)];
  return expand(add(`*`(op(subsop(i = apply_leibniz(f)(uu[i]),uu))),i=1..nops(uu)));
 elif type(u,`^`) then
  v,n := op(u);
  return n * v^(n-1) * apply_leibniz(f)(v);
 elif type(u,rational) then
  return 0;
 else
  return f(u);
 fi;
end:

apply_leibniz_mod := (f,m::posint) -> proc(u)
 local n,v,uu;
 
 if type(u,`+`) or type(u,list) or type(u,set) then
  return map(apply_leibniz(f),u);
 elif type(u,`*`) then
  uu := [op(u)];
  return modp(expand(add(`*`(op(subsop(i = apply_leibniz(f)(uu[i]),uu))),i=1..nops(uu))),m);
 elif type(u,`^`) then
  v,n := op(u);
  if modp(n,m) = 0 then
   return 0;
  else 
   return modp(expand(n * v^(n-1) * apply_leibniz(f)(v)),m);
  fi;
 elif type(u,rational) then
  return 0;
 else
  return f(u);
 fi;
end:
