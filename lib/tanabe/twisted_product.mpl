grassmann_count := (q) -> (n::nonnegint,d::nonnegint) ->
 factor(mul(q^(n-i)-1,i=0..d-1)/mul(q^(d-i)-1,i=0..d-1));

splitting_count := (q) -> (n::nonnegint,m::nonnegint) ->
 grassmann_count(q)(n+m,n) * q^(n*m);

`indices/twisted_product/A` := proc(r::nonnegint)
 option remember;
 local U,V,u,v,e;
 
 if r = 0 then return [[]]; fi;
 if not(type(r,posint)) then return FAIL; fi;
 
 U := `indices/twisted_product/A`(r-1);
 V := NULL;
 for u in U do
  e := d-1-`+`(op(u));
  V := V,seq([op(u),v],v=0..e);
 od;
 return [V];
end:

`is_element/twisted_product/A` := (r::nonnegint) -> proc(f)
 if not(type(f,table)) then
  return false;
 fi;

 return evalb({indices(f)} = {op(`indices/twisted_product/A`(r))});
end:

`is_equal/twisted_product/A` := (r::nonnegint) -> proc(f,g)
 local U,u;
 
 U := `indices/twisted_product/A`(r);

 for u in U do
  if simplify(f[op(u)]-g[op(u)]) <> 0 then
   return false;
  fi;
 od;

 return true;
end:

`to_list/twisted_product/A` := (r::nonnegint) -> (f) -> [seq(f[op(u)],u in `indices/twisted_product/A`(r))];
`from_symbol/twisted_product/A` := (r::nonnegint) -> (f) -> table([seq(op(u)=f[op(u)],u in `indices/twisted_product/A`(r))]);

`zero/twisted_product/A` := proc(r::nonnegint)
 option remember;
 table([seq(op(u)=0,u in `indices/twisted_product/A`(r))]);
end:

`one/twisted_product/A` := proc(r::nonnegint)
 option remember;
 table([seq(op(u)=1,u in `indices/twisted_product/A`(r))]);
end:

`delta/twisted_product/A` := proc(r::nonnegint)
 option remember;
 table([seq(op(u)=`if`(u=[0$r],1,0),u in `indices/twisted_product/A`(r))]);
end:

`plus/twisted_product/A` := (r::nonnegint) -> proc(f,g)
 table([seq(op(u) = f[op(u)] + g[op(u)],u in `indices/twisted_product/A`(r))]);
end:

`minus/twisted_product/A` := (r::nonnegint) -> proc(f,g)
 table([seq(op(u) = f[op(u)] - g[op(u)],u in `indices/twisted_product/A`(r))]);
end:

`dot/twisted_product/A` := (r::nonnegint) -> proc(f,g)
 table([seq(op(u) = f[op(u)] * g[op(u)],u in `indices/twisted_product/A`(r))]);
end:

`scalar_times/twisted_product/A` := (r::nonnegint) -> proc(c,f)
 table([seq(op(u) = c * f[op(u)],u in `indices/twisted_product/A`(r))]);
end:

`mu/twisted_product/A` := (r::nonnegint) -> proc(u,v)
 option remember;
 
 mul(splitting_count(q)(u[i],v[i]),i=1..r) *
 q^add(add(u[i]*v[j]+2*u[j]*v[i],j=i+1..r),i=1..r-1);
end:

`star/twisted_product/A` := (r::nonnegint) -> proc(f,g)
 local h,X,u,v,w,x;
 
 h := table([seq(op(u)=0,u in `indices/twisted_product/A`(r))]);
 
 X := `indices/twisted_product/A`(2*r);
 for x in X do
  u := [op(1..r,x)];
  v := [op(r+1..2*r,x)];
  w := u +~ v;
  h[op(w)] := h[op(w)] + `mu/twisted_product/A`(r)(u,v) * f[op(u)] * g[op(v)];
 od;

 return eval(h);
end:

