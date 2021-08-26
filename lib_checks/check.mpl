kernelopts(assertlevel=1):
assert_count := 0;
assert_verbosely := false;
assert_stop_on_fail := true;

#@ _ASSERT 
_ASSERT := proc(p,s::string)
 global assert_count,assert_verbosely,assert_stop_on_fail,assert_fail_data;
 assert_count := assert_count+1;
 if assert_verbosely then printf("Checking: %s\n",s); fi;
 if not p then
  assert_fail_data := args[3..-1];
  if assert_stop_on_fail then
   error cat("Assertion failed: ",s);
  else
   printf(cat("Assertion failed: ",s,"\n"));
  fi;
 fi;
end:

######################################################################

# checklist is a list of checking functions.  check_all() runs all
# the checking functions in the list.  add_check() adds a function 
# to the list.

checklist := []: #@ checklist 

check_all := proc() 
 global assert_count;
 local C;

 assert_count := 0;

 for C in checklist do C(); od:
end:

add_check := proc(C)
 global checklist;

 checklist := [op(checklist),C];
end:

######################################################################

num_steps := 100;

check_set_generic := proc(S::string,params := [])
 local
  small_context,params0,
  is_element,random_element,list_elements,count_elements,is_equal,is_leq,
  `has/is_element`,`has/random_element`,`has/list_elements`,
  `has/count_elements`,`has/is_equal`,`has/is_leq`,
  p,x,y,t,i,j,L,L_full,L_rand,L_rand_ok,L_rand_bad,found;

 printf("\nChecking %s\n",S);

 is_element := eval(convert(cat("is_small_element/",S),name));
 
 if type(is_element,procedure) then
  small_context := true;
  is_element      := eval(convert(cat("is_small_element/"    ,S),name)); 
  random_element  := eval(convert(cat("random_small_element/",S),name));
  list_elements   := eval(convert(cat("list_small_elements/" ,S),name));
  count_elements  := eval(convert(cat("count_small_elements/",S),name));
  is_equal        := eval(convert(cat("is_equal/"            ,S),name)); 
  is_leq          := eval(convert(cat("is_leq/"              ,S),name));
  printf("Elements are filtered by size\n");
 else
  small_context := false;
  is_element      := eval(convert(cat("is_element/"    ,S),name)); 
  random_element  := eval(convert(cat("random_element/",S),name));
  list_elements   := eval(convert(cat("list_elements/" ,S),name));
  count_elements  := eval(convert(cat("count_elements/",S),name));
  is_equal        := eval(convert(cat("is_equal/"      ,S),name)); 
  is_leq          := eval(convert(cat("is_leq/"        ,S),name)); 
 fi;
 
 `has/is_element`     := type(is_element,procedure);
 `has/random_element` := type(random_element,procedure);
 `has/list_elements`  := type(list_elements,procedure);
 `has/count_elements` := type(count_elements,procedure);
 `has/is_equal`       := type(is_equal,procedure);
 `has/is_leq`         := type(is_leq,procedure);

 if `has/is_element` then
  for p in params do is_element := eval(is_element(op(p))); od;
 elif is_element <> NULL then
  printf("Warning: no is_element function has been defined.\n");
 fi;

 if `has/random_element` then
  for p in params do random_element := eval(random_element(op(p))); od;
 elif random_element <> NULL then
  printf("Warning: no random_element function has been defined.\n");
 fi;

 if `has/list_elements` then
  for p in params do list_elements := eval(list_elements(op(p))); od;
 elif list_elements <> NULL then
  printf("Warning: no list_elements function has been defined.\n");
 fi;

 if `has/count_elements` then
  for p in params do count_elements := eval(count_elements(op(p))); od;
 elif count_elements <> NULL then
  printf("Warning: no count_elements function has been defined.\n");
 fi;

 params0 := params;
 if small_context then
  params0 := [op(1..-2,params)];
 fi;
 
 if `has/is_equal` then
  for p in params0 do is_equal := eval(is_equal(op(p))); od;
 else
  is_equal := (x,y) -> evalb(x = y);
 fi;

 if `has/is_leq` then
  for p in params0 do is_leq := eval(is_leq(op(p))); od;
 elif is_leq <> NULL then
  printf("Warning: no is_leq function has been defined.\n");
 fi;

 L := NULL;
 
 if `has/random_element` and `has/is_element` then
  printf("Checking is_element on random elements: ");
  L_rand := [seq(random_element(),i=1..10)];
  L_rand_ok,L_rand_bad := selectremove(x -> (x <> FAIL),L_rand);
  t := `and`(true,op(map(is_element,L_rand_ok)));
  if t then
   L := L_rand_ok;
   if L_rand_bad = [] then
    printf("OK\n");
   elif L_rand_ok <> [] then
    printf("OK (but some examples could not be generated)\n");
   else
    printf("Could not generate any examples\n");
   fi;
  else
   printf("FAIL\n");
  fi;
 fi;

 if `has/list_elements` and `has/is_element` then
  printf("Checking is_element on listed elements: ");
  L_full := list_elements;
  if type([L_full],[list]) then
   L := L_full;
   t := `and`(op(map(is_element,L_full)));
   if t then
    printf("OK (%d elements)\n",nops(L_full));
   else 
    printf("FAIL\n");
   fi;
  else
   printf("Element list is not a list\n");
   L := [];
   L_full := [];
  fi;
 fi;

 if `has/random_element` and `has/list_elements` and `has/is_element` 
     and L_rand_ok <> [] then
  printf("Comparing random elements and listed elements: ");
  t := true;
  for x in L_rand_ok do
   found := false;
   for y in L_full do
    if is_equal(x,y) then
     found := true;
     break;
    fi;
   od;
   if not found then
    t := false;
    break;
   fi;
  od;
  printf(`if`(t,"OK\n","FAIL\n"));
 fi;

 if L <> NULL and `has/is_equal` then
  printf("Checking is_equal: ");
  t := true;
  for i from 1 to nops(L) do
   t := t and is_equal(L[i],L[i]);
   if not t then break; fi;
   if `has/list_elements` then
    for j from i+1 to nops(L) do
     t := t and not(is_equal(L[i],L[j]));
     if not t then break; fi;
    od;
   fi;
   if not t then break; fi;
  od;
  printf(`if`(t,"OK\n","FAIL\n"));  
 fi;
 
 if `has/list_elements` and `has/count_elements` then
  printf("Checking count_elements (%A) vs listed elements: ",count_elements);
  t := evalb(count_elements = nops(L_full));
  printf(`if`(t,"OK\n","FAIL\n"));
 fi;
end:

######################################################################

check_map_generic := proc(fs::string,X::string,Y::string,params_f,params_X,params_Y)
 global reason;
 local P_f,P_X,P_Y,list_elements_X,random_element_X,is_element_X,is_element_Y,p,x,y,L,f,ok,i;

 printf("Checking %s : %s -> %s\n",fs,X,Y);

 P_f := `if`(nargs > 3,params_f,[]);
 P_X := `if`(nargs > 4,params_X,P_f);
 P_Y := `if`(nargs > 5,params_Y,P_X);

 list_elements_X := eval(convert(cat("list_elements/",X),name));
 if list_elements_X <> NULL then
  for p in P_X do
   list_elements_X := eval(list_elements_X(op(p)));
  od;
  L := list_elements_X;
 else
  random_element_X := eval(convert(cat("random_element/",X),name));
  if random_element_X = NULL then
   error sprintf("Neither list_elements/%s nor random_element/%s is defined",X,X);
  fi;
  for p in P_X do
   random_element_X := eval(random_element_X(op(p)));
  od;
  L := [seq(random_element_X(),i=1..num_steps)];
 fi;

 f := eval(convert(fs,name));
 for p in P_f do f := eval(f(op(p))); od;
 
 is_element_X := eval(convert(cat("is_element/",X),name));
 for p in P_X do
  is_element_X := eval(is_element_X(op(p)));
 od;

 is_element_Y := eval(convert(cat("is_element/",Y),name));
 for p in P_Y do
  is_element_Y := eval(is_element_Y(op(p)));
 od;

 ok := true;
 for x in L do
  if not(is_element_X(x)) then
   ok := false;
   reason := ["x is not in X",x];
   break;
  fi;
  
  y := f(x);

  if not(is_element_Y(y)) then
   ok := false;
   reason := ["f(x) = y is not in Y",x,y];
   break;
  fi;
 od:

 printf(`if`(ok,"OK\n","FAIL\n"));
end:

######################################################################

check_binop_generic :=
 proc(fs::string,X::string,Y::string,Z::string,params_f,params_X,params_Y,params_Z)
 global reason;
 local P_f,P_X,P_Y,P_Z,
       list_elements_X,random_element_X,is_element_X,
       list_elements_Y,random_element_Y,is_element_Y,
       is_element_Z,p,x,y,z,L_X,L_Y,f,ok,ns,curry,i;

 printf("Checking %s : %s x %s -> %s\n",fs,X,Y,Z);

 P_f := `if`(nargs > 3,params_f,[]);
 P_X := `if`(nargs > 4,params_X,P_f);
 P_Y := `if`(nargs > 5,params_Y,P_X);
 P_Z := `if`(nargs > 5,params_Z,P_Y);
 curry := false;

 if member("curry",[_rest]) then
  curry := true;
 fi;
 
 ns := ceil(sqrt(evalf(num_steps)));

 list_elements_X := eval(convert(cat("list_elements/",X),name));
 if list_elements_X <> NULL then
  for p in P_X do
   list_elements_X := eval(list_elements_X(op(p)));
  od;
  L_X := list_elements_X;
 else
  random_element_X := eval(convert(cat("random_element/",X),name));
  if random_element_X = NULL then
   error sprintf("Neither list_elements/%s nor random_element/%s is defined",X,X);
  fi;
  for p in P_X do
   random_element_X := eval(random_element_X(op(p)));
  od;
  L_X := [seq(random_element_X(),i=1..ns)];
 fi;

 list_elements_Y := eval(convert(cat("list_elements/",Y),name));
 if list_elements_Y <> NULL then
  for p in P_Y do
   list_elements_Y := eval(list_elements_Y(op(p)));
  od;
  L_Y := list_elements_Y;
 else
  random_element_Y := eval(convert(cat("random_element/",Y),name));
  if random_element_Y = NULL then
   error sprintf("Neither list_elements/%s nor random_element/%s is defined",Y,Y);
  fi;
  for p in P_Y do
   random_element_Y := eval(random_element_Y(op(p)));
  od;
  L_Y := [seq(random_element_Y(),i=1..ns)];
 fi;

 f := eval(convert(fs,name));
 for p in P_f do f := eval(f(op(p))); od;
 
 is_element_X := eval(convert(cat("is_element/",X),name));
 for p in P_X do
  is_element_X := eval(is_element_X(op(p)));
 od;

 is_element_Y := eval(convert(cat("is_element/",Y),name));
 for p in P_Y do
  is_element_Y := eval(is_element_Y(op(p)));
 od;

 is_element_Z := eval(convert(cat("is_element/",Z),name));
 for p in P_Z do
  is_element_Z := eval(is_element_Z(op(p)));
 od;

 ok := true;
 for x in L_X do
  if not(is_element_X(x)) then
   ok := false;
   reason := ["x is not in X",x];
   break;
  fi;

  for y in L_Y do  
   if not(is_element_Y(y)) then
    ok := false;
    reason := ["y is not in Y",y];
    break;
   fi;

   if curry then
    z := f(x,y);
   else
    z := f(x)(y);
   fi;
   
   if not(is_element_Z(z)) then
    ok := false;
    reason := ["f(x,y) = z is not in Z",x,y,z];
    break;
   fi;
  od;
 od:

 printf(`if`(ok,"OK\n","FAIL\n"));
end:

######################################################################

check_operad := proc(O::string,params,A,B,C)
 global reason;
 local is_element,is_equal,random_element,eta,gamma,
       x,i,p,q,qp,Fp,Fq,Fqp,U,V,W,ok,c,b;

 printf("Checking operad structure for %s: ",O);

 is_element     := eval(convert(cat("is_element/",O),name));
 is_equal       := eval(convert(cat("is_equal/",O),name));
 random_element := eval(convert(cat("random_element/",O),name));
 eta            := eval(convert(cat("eta/",O),name));
 gamma          := eval(convert(cat("gamma/",O),name));

 for x in params do 
  is_element     := eval(is_element(op(x)));
  is_equal       := eval(is_equal(op(x)));
  random_element := eval(random_element(op(x)));
  eta            := eval(eta(op(x)));
  gamma          := eval(gamma(op(x)));
 od:

 for i from 1 to num_steps do
  p := `random_element/epi`(A,B)();
  q := `random_element/epi`(B,C)();
  qp := `compose/maps`(A,B,C)(p,q);
  Fp := fibres(A,B)(p);
  Fq := fibres(B,C)(q);
  Fqp := fibres(A,C)(qp);
  U := random_element(C)();
  V := table({seq(c = random_element(Fq[c])(),c in C)});
  W := table({seq(b = random_element(Fp[b])(),b in B)});
  ok := `check_gamma_axiom`(A,B,C,p,q,U,V,W,
   is_element,is_equal,gamma);
  if not ok then printf("FAIL\n");
   reason := ["gamma axiom failed",A,B,C,eval(p),eval(q),eval(U),eval(V),eval(W),reason];
   return false; 
  fi;
 od:

 printf("OK\n");
end:

check_operad_morphism := proc(f::string,f_params,
                              C::string,C_params,
                              D::string,D_params,
                              A,B)
 global reason;
 local is_el_CC,is_equal_CC,gamma_CC,
       is_el_DD,is_equal_DD,gamma_DD,
       rand_CC,phi,x,i,p,Fp,U,V,ok,b;

 printf("Checking operad morphism %s : %s -> %s\n",f,C,D);

 is_el_CC    := eval(convert(cat("is_element/",C),name));
 is_equal_CC := eval(convert(cat("is_equal/",C),name));
 gamma_CC    := eval(convert(cat("gamma/",C),name));
 rand_CC     := eval(convert(cat("random_element/",C),name));

 is_el_DD    := eval(convert(cat("is_element/",D),name));
 is_equal_DD := eval(convert(cat("is_equal/",D),name));
 gamma_DD    := eval(convert(cat("gamma/",D),name));

 phi         := eval(convert(f,name));

 for x in f_params do 
  phi := eval(phi(op(x)));
 od:

 for x in C_params do 
  is_el_CC    := eval(is_el_CC(op(x)));
  is_equal_CC := eval(is_equal_CC(op(x)));
  gamma_CC    := eval(gamma_CC(op(x)));
  rand_CC     := eval(rand_CC(op(x)));
 od;

 for x in D_params do 
  is_el_DD    := eval(is_el_DD(op(x)));
  is_equal_DD := eval(is_equal_DD(op(x)));
  gamma_DD    := eval(gamma_DD(op(x)));
 od:

 for i from 1 to num_steps do
  p := `random_element/epi`(A,B)();
  Fp := fibres(A,B)(p);
  U := rand_CC(B)();
  V := table({seq(b = rand_CC(Fp[b])(),b in B)});
  ok := `check_operad_morphism_axiom`(A,B,p,U,V,
      is_el_CC,is_equal_CC,gamma_CC,
      is_el_DD,is_equal_DD,gamma_DD,
      phi);
  if not ok then printf("FAIL\n");
   reason := ["operad morphism axiom failed",A,B,eval(p),eval(U),eval(V),reason];
   return false; 
  fi;
 od:

 printf("OK\n");
end:

######################################################################

check_semioperad := proc(O::string,params,L)
 global reason;
 local is_element,is_equal,random_element,gamma,
       x,J,L_,i,k,jj,ii,H,U,V,W,ok,j0,k0;

 printf("Checking operad structure for %s: ",O);

 is_element     := eval(convert(cat("is_element/",O),name));
 is_equal       := eval(convert(cat("is_equal/",O),name));
 random_element := eval(convert(cat("random_element/",O),name));
 gamma          := eval(convert(cat("gamma/",O),name));

 for x in params do 
  is_element     := eval(is_element(op(x)));
  is_equal       := eval(is_equal(op(x)));
  random_element := eval(random_element(op(x)));
  gamma          := eval(gamma(op(x)));
 od:

 J := map(nops,L);
 L_ := map(op,L);
 k := nops(J);
 jj := `+`(op(J));
 ii := `+`(op(L_));
 H := [seq(`+`(op(L[k0])),k0=1..k)];

 for i from 1 to num_steps do
  U := random_element(k)();
  V := [seq(random_element(J[k0])(),k0 = 1..k)];
  W := [seq([seq(random_element(L[k0][j0])(),j0=1..J[k0])],k0=1..k)];
  ok := `check_semi_gamma_axiom`(L,U,V,W,
   is_element,is_equal,gamma);
  if not ok then printf("FAIL\n");
   reason := ["gamma axiom failed",L,eval(U),eval(V),eval(W),reason];
   return false; 
  fi;
 od:

 printf("OK\n");
end:

######################################################################

check_semi_circ := proc(O::string,params,l,m,n)
 global reason;
 local is_element,is_equal,random_element,circ,
       x,c,i,j,k,U,V,W,ok;

 printf("Checking operad structure for %s: ",O);

 is_element     := eval(convert(cat("is_element/",O),name));
 is_equal       := eval(convert(cat("is_equal/",O),name));
 random_element := eval(convert(cat("random_element/",O),name));
 circ           := eval(convert(cat("circ/",O),name));

 for x in params do 
  is_element     := eval(is_element(op(x)));
  is_equal       := eval(is_equal(op(x)));
  random_element := eval(random_element(op(x)));
  circ           := eval(circ(op(x)));
 od:

 for c from 1 to num_steps do
  U := random_element(l)();
  V := random_element(m)();
  W := random_element(n)();
  i := rand(1..l)();
  j := rand(1..m)();
  ok := `check_semi_circ_axiom_nested`(i,j,l,m,n,U,V,W,
   is_element,is_equal,circ);
  if not ok then printf("FAIL\n");
   reason := ["nested circ axiom failed",i,j,l,m,n,eval(U),eval(V),eval(W),reason];
   return false; 
  fi;

  i := rand(1..(l-1))();
  k := rand((i+1)..l)();
  ok := `check_semi_circ_axiom_disjoint`(i,k,l,m,n,U,V,W,
   is_element,is_equal,circ);
  if not ok then printf("FAIL\n");
   reason := ["disjoint circ axiom failed",i,j,l,m,n,eval(U),eval(V),eval(W),reason];
   return false; 
  fi;
 od:

 printf("OK\n");
end:
