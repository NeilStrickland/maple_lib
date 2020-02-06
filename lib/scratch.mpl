`mu/BA` := proc()
 apply_bilinear_assoc(`mu_aux0/BA`,`bar/BA`())(args);
 local xx,ca,cb,pa,pb;
 if nargs > 2 then
  return `mu/BA`(`mu/BA`(a,b),args[3..-1]);
 fi;
 if type(a,numeric) or type(b,numeric) then
  return expand(a*b);
 elif type(a,`+`) then
  return map(`mu/BA`,a,b);
 elif type(b,`+`) then
  return map2(`mu/BA`,a,b);
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
 if type(pa,specfunc(anything,`bar/BA`)) and
    type(pb,specfunc(anything,`bar/BA`)) then
  return expand(ca*cb*`mu_aux0/BA`(pa,pb));
 else
  return('`mu/BA`'(args))
 fi;
end:


`mu/EA` := proc()
 apply_linear_assoc(`mu0/EA`,`bar/EA`())(args);
end:


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
