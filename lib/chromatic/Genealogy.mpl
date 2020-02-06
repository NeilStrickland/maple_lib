#@ Not autoload

E := proc(u)
 local n,i;
 if type(u,`+`) then
  return(map(E,u));
 else
  return('E'(u));
 fi;
end:

H := proc(u)
 local n,i,J;
 if type(u,`+`) then
  return(map(H,u));
 else
  return('H'(u));
 fi;
end:

P := proc(u)
 local n,i;
 if type(u,`+`) then
  return(map(P,u));
 else
  return('P'(u));
 fi;
end:
 
o := proc(a,b)
 if a=0 or b=0 then
  return(0);
 elif type(b,`+`) then
  return(map2(o,a,b));
 elif type(a,indexed) and op(0,a)=x and op(2,a)=[] then
  return(b);
 elif type(b,indexed) and op(0,b)=x and op(2,b)=[] then
  return(a);
 else
  return('o'(args));
 fi;
end:

is_o := proc(u)
 type(u,specfunc(anything,o));
end:

SpherePi := proc(n,m)
 local stem,is_stable,G;
 stem := n-m;
 is_stable := evalb(m>stem+1);

 if stem<0 or m<=0 or (n>1 and m=1) then
  return(Group());
 elif stem=0 then
  return(Group([],[x[n,[]]]));
 elif is_stable then
  G := StableSpherePi(stem);
  return(Group(map(a -> x[m,op(2,a)],op(1,G))));
 else
  return('SpherePi'(n,m));
 fi;
end:

Source := proc(a)
 if type(a,indexed) and op(0,a) = x then
  return(op(1,a) + `+`(op(op(2,a))));
 elif is_o(a) and nops(a) > 0 then
  return Source(op(nops(a),a))
 else
  return('Source'(args));
 fi; 
end:

Target := proc(a)
 if type(a,indexed) and op(0,a) = x then
  return(op(1,a));
 elif is_o(a) and nops(a) > 0 then
  return Target(op(1,a))
 else
  return('Target'(args));
 fi; 
end:

Stem := proc(a) Source(a) - Target(a); end:

IsAdmissible := proc(a)
 local m,J,r,i;
 if type(a,indexed) and op(0,a) = x then
  m := op(1,a);
  J := op(2,a);
  r := nops(J);
  if r>0 and J[1] >= m then 
   return(false);
  fi;
  for i from 1 to r-1 do
   if J[i+1] > 2*J[i] then
    return(false);
   fi;
  od;
  return(true);
 else
  return('IsAdmissible'(args));
 fi; 
end:

# 1-stem

SpherePi( 3, 2) := Group([],[x[2,[1]]]):
SpherePi( 4, 3) := Group([x[3,[1]]]):

StableSpherePi( 1) := Group([x[infinity,[1]]]):

# 2-stem 

SpherePi( 4, 2) := Group([x[2,[1,1]]]):
SpherePi( 5, 3) := Group([x[3,[1,1]]]):

StableSpherePi( 2) := Group([x[infinity,[1,1]]]):

# 3-stem

SpherePi( 5, 2) := Group([x[2,[1,1,1]]]):
SpherePi( 6, 3) := Group([x[3,[2,1]],
                          x[3,[1,1,1]]]):
SpherePi( 7, 4) := Group([x[4,[2,1]],
                          x[4,[1,1,1]]],
                         [x[4,[3]]]):

StableSpherePi( 3) := Group([x[infinity,[3]],
		             x[infinity,[2,1]],
		             x[infinity,[1,1,1]]]):

# 4-stem

SpherePi( 6, 2) := Group([x[2,[1,1,1,1]],
                          x[2,[1,2,1]]]):
SpherePi( 7, 3) := Group([x[3,[2,1,1]]]):
SpherePi( 8, 4) := Group([x[4,[3,1]],
                          x[4,[2,1,1]]]):
SpherePi( 9, 5) := Group([x[5,[3,1]]]):

StableSpherePi( 4) := Group([]):

# 5-stem 

SpherePi( 7, 2) := Group([x[2,[1,2,1,1]]]):
SpherePi( 8, 3) := Group([x[3,[2,1,1,1]]]):
SpherePi( 9, 4) := Group([x[4,[3,1,1]],
                          x[4,[2,1,1,1]]]):
SpherePi(10, 5) := Group([x[5,[3,1,1]]]):
SpherePi(11, 6) := Group([],[x[6,[5,0]]]):

StableSpherePi( 5) := Group([]):

# 6-stem 

SpherePi( 8, 2) := Group([x[2,[1,2,1,1,1]]]):
SpherePi( 9, 3) := Group([]):
SpherePi(10, 4) := Group([x[4,[3,3]],
                          x[4,[3,2,1]],
                          x[4,[3,1,1,1]]]):
SpherePi(11, 5) := Group([x[5,[3,3]]]):
SpherePi(12, 6) := Group([x[6,[3,3]]]):
SpherePi(13, 7) := Group([x[7,[3,3]]]):

StableSpherePi( 6) := Group([x[infinity,[3,3]]]):

# 7-stem 

SpherePi( 9, 2) := Group([]):
SpherePi(10, 3) := Group([]):
SpherePi(11, 4) := Group([]):
SpherePi(12, 5) := Group([x[5,[4,1,1,1]]]):
SpherePi(13, 6) := Group([x[6,[5,1,1]],
                          x[6,[4,1,1,1]]]):
SpherePi(14, 7) := Group([x[7,[6,1]],
                          x[7,[5,1,1]],
                          x[7,[4,1,1,1]]]):
SpherePi(15, 8) := Group([x[8,[6,1]]],[x[8,[7]]]):

StableSpherePi( 7) := Group([x[infinity,[7]],
		             x[infinity,[6,1]],
                             x[infinity,[5,1,1]],
                             x[infinity,[4,1,1,1]]]):

# 8-stem 

SpherePi(10, 2) := Group([]):
SpherePi(11, 3) := Group([x[3,[2,3,3]]]):
SpherePi(12, 4) := Group([x[4,[2,3,3]]]):
SpherePi(13, 5) := Group([x[5,[2,3,3]]]):
SpherePi(14, 6) := Group([x[6,[5,3]],
                          x[6,[5,2,1]],
                          x[6,[5,1,1,1]],
                          x[6,[2,3,3]]]):
SpherePi(15, 7) := Group([x[7,[6,1,1]],
                          x[7,[5,3]],
                          x[7,[2,3,3]]]):
SpherePi(16, 8) := Group([x[8,[7,1]],
                          x[8,[6,1,1]],
                          x[8,[5,3]],
                          x[8,[2,3,3]]]):
SpherePi(17, 9) := Group([x[9,[7,1]],
                          x[9,[5,3]],
                          x[9,[2,3,3]]]):

StableSpherePi( 8) := Group([x[infinity,[5,3]],
                             x[infinity,[2,3,3]]]):

# 9-stem 

SpherePi(11, 2) := Group([x[2,[1,2,3,3]]]):
SpherePi(12, 3) := Group([x[3,[2,4,1,1,1]],
                          x[3,[1,2,3,3]]]):
SpherePi(13, 4) := Group([x[4,[3,3,3]],
                          x[4,[2,4,1,1,1]],
                          x[4,[1,2,3,3]]]):
SpherePi(14, 5) := Group([x[5,[3,3,3]],
                          x[5,[2,4,1,1,1]],
                          x[5,[1,2,3,3]]]):
SpherePi(15, 6) := Group([x[6,[3,3,3]],
                          x[6,[2,4,1,1,1]],
                          x[6,[1,2,3,3]]]):
SpherePi(16, 7) := Group([x[7,[6,1,1,1]],
                          x[7,[3,3,3]],
                          x[7,[2,4,1,1,1]],
                          x[7,[1,2,3,3]]]):
SpherePi(17, 8) := Group([x[8,[7,1,1]],
                          x[8,[6,1,1,1]],
                          x[8,[3,3,3]],
                          x[8,[2,4,1,1,1]],
                          x[8,[1,2,3,3]]]):
SpherePi(18, 9) := Group([x[9,[7,1,1]],
                          x[9,[3,3,3]],
                          x[9,[2,4,1,1,1]],
                          x[9,[1,2,3,3]]]):
SpherePi(19,10) := Group([x[10,[3,3,3]],
                          x[10,[2,4,1,1,1]],
                          x[10,[1,2,3,3]]],
                         [x[10,[9,0]]]):

StableSpherePi( 9) := Group([x[infinity,[3,3,3]],
                             x[infinity,[2,4,1,1,1]],
                             x[infinity,[1,2,3,3]]]):

# 10-stem 

SpherePi(12, 2) := Group([x[2,[1,2,4,1,1,1]],
                          x[2,[1,1,2,3,3]]]):
SpherePi(13, 3) := Group([x[3,[2,2,3,3]],
                          x[3,[1,2,4,1,1,1]],
                          x[3,[1,1,2,3,3]]]):
SpherePi(14, 4) := Group([x[4,[3,6,1]],
                          x[4,[3,5,1,1]],
                          x[4,[3,4,1,1,1]],
                          x[4,[2,2,3,3]],
                          x[4,[1,2,4,1,1,1]],
                          x[4,[1,1,2,3,3]]]):
SpherePi(15, 5) := Group([x[5,[4,3,3]],
                          x[5,[2,2,3,3]],
                          x[5,[1,2,4,1,1,1]],
                          x[5,[1,1,2,3,3]]]):
SpherePi(16, 6) := Group([x[6,[4,3,3]],
                          x[6,[2,2,3,3]],
                          x[6,[1,2,4,1,1,1]],
                          x[6,[1,1,2,3,3]]]):
SpherePi(17, 7) := Group([x[7,[4,3,3]],
                          x[7,[2,2,3,3]],
                          x[7,[1,2,4,1,1,1]],
                          x[7,[1,1,2,3,3]]]):
SpherePi(18, 8) := Group([x[8,[7,3]],
                          x[8,[7,2,1]],
                          x[8,[7,1,1,1]],
                          x[8,[4,3,3]],
                          x[8,[2,2,3,3]],
                          x[8,[1,2,4,1,1,1]],
                          x[8,[1,1,2,3,3]]]):
SpherePi(19, 9) := Group([x[9,[7,3]],
                          x[9,[7,2,1]],
                          x[9,[7,1,1,1]],
                          x[9,[1,2,4,1,1,1]]]):
SpherePi(20,10) := Group([x[10,[7,3]],
                          x[10,[7,2,1]],
                          x[10,[1,2,4,1,1,1]]]):
SpherePi(21,11) := Group([x[11,[7,3]],
                          x[11,[1,2,4,1,1,1]]]):

StableSpherePi(10) := Group([x[infinity,[1,2,4,1,1,1]]]):

# 11-stem 

SpherePi(13, 2) := Group([x[2,[1,2,2,3,3]],
                          x[2,[1,1,1,2,3,3]],
                          x[2,[1,1,2,4,1,1,1]]]):
SpherePi(14, 3) := Group([x[3,[2,3,3,3]],
                          x[3,[2,2,4,1,1,1]],
                          x[3,[2,1,2,3,3]],
                          x[3,[1,1,2,4,1,1,1]]]):
SpherePi(15, 4) := Group([x[4,[3,6,1,1]],
                          x[4,[3,5,3]],
                          x[4,[3,2,3,3]],
                          x[4,[2,3,3,3]],
                          x[4,[2,2,4,1,1,1]],
                          x[4,[2,1,2,3,3]],
                          x[4,[1,1,2,4,1,1,1]]]):
SpherePi(16, 5) := Group([x[5,[4,4,1,1,1]],
                          x[5,[3,5,3]],
                          x[5,[3,2,3,3]],
                          x[5,[2,2,4,1,1,1]],
                          x[5,[1,1,2,4,1,1,1]]]):
SpherePi(17, 6) := Group([x[6,[5,3,3]],
                          x[6,[4,4,1,1,1]],
                          x[6,[2,2,4,1,1,1]],
                          x[6,[1,1,2,4,1,1,1]]]):
SpherePi(18, 7) := Group([x[7,[5,3,3]],
                          x[7,[4,4,1,1,1]],
                          x[7,[2,2,4,1,1,1]],
                          x[7,[1,1,2,4,1,1,1]]]):
SpherePi(19, 8) := Group([x[8,[5,3,3]],
                          x[8,[4,4,1,1,1]],
                          x[8,[2,2,4,1,1,1]],
                          x[8,[1,1,2,4,1,1,1]]]):
SpherePi(20, 9) := Group([x[9,[5,3,3]],
                          x[9,[4,4,1,1,1]],
                          x[9,[2,2,4,1,1,1]],
                          x[9,[1,1,2,4,1,1,1]]]):
SpherePi(21,10) := Group([x[10,[4,4,1,1,1]],
                          x[10,[2,2,4,1,1,1]],
                          x[10,[1,1,2,4,1,1,1]]]):
SpherePi(22,11) := Group([x[11,[4,4,1,1,1]],
                          x[11,[2,2,4,1,1,1]],
                          x[11,[1,1,2,4,1,1,1]]]):
SpherePi(23,12) := Group([x[12,[4,4,1,1,1]],
                          x[12,[2,2,4,1,1,1]],
                          x[12,[1,1,2,4,1,1,1]]]):

StableSpherePi(11) := Group([x[infinity,[4,4,1,1,1]],
                             x[infinity,[2,2,4,1,1,1]],
                             x[infinity,[1,1,2,4,1,1,1]]]):

# 12-stem 

StableSpherePi(12) := Group([]):

# 13-stem 

StableSpherePi(13) := Group([]):

# 14-stem 

StableSpherePi(14) := Group([x[infinity,[7,7]],
                             x[infinity,[6,2,3,3]]]):


N := 11:
degrees_above := (k) -> [seq(k+i,i=0..N),infinity];

for n in degrees_above(1) do
 TodaName(x[n,[]]) := iota[n]:
od:

for n in degrees_above(2) do 
 TodaName(x[n,[1]]) := eta[n]:
 TodaName(x[n,[1,1]]) := o(eta[n],eta[n+1]):
 TodaName(x[n,[1,2,3,3]]) := o(eta[n],epsilon[n+1]):
 TodaName(x[n,[1,2,4,1,1,1]]) := o(eta[n],mu[n+1]):
od:

for n in degrees_above(3) do 
 TodaName(x[n,[2,3,3]]) := epsilon[n]:
 TodaName(x[n,[2,4,1,1,1]]) := mu[n]:
od:

for n in degrees_above(4) do
 TodaName(x[n,[3]]) := nu[n]:
 TodaName(x[n,[3,3,3]]) := o(nu[n],nu[n+3],nu[n+6]):
od:

for n in degrees_above(5) do 
 TodaName(x[n,[4,4,1,1,1]]) := zeta[n]:
 TodaName(x[n,[2,2,4,1,1,1]]) := 2 * zeta[n]:
 TodaName(x[n,[1,1,2,4,1,1,1]]) := 4 * zeta[n]:
 TodaName(x[n,[3,3]]) := o(nu[n],nu[n+3]):
 TodaName(x[n,[2,1]]) :=  2 * nu[n]:
 TodaName(x[n,[1,1,1]]) :=  4 * nu[n]:
od:

for n in degrees_above(6) do
 TodaName(x[n,[5,3]]) := nubar[n]:
od:

for n in degrees_above(8) do
 TodaName(x[n,[7]]) := sigma[n]:
od:

for n in degrees_above(9) do
 TodaName(x[n,[6,1]]) := 2*sigma[n]:
 TodaName(x[n,[5,1,1]]) := 4*sigma[n]:
 TodaName(x[n,[4,1,1,1]]) := 8*sigma[n]:
od:

TodaName(x[2,[1,1,1,1]]) := - o(eta[2],nuprime):
TodaName(x[8,[7]]) := sigma[8]:
TodaName(x[2,[1,2,2,3,3]]) := 3 * o(eta[2],epsilonprime):
TodaName(x[2,[1,2,2,4,1,1,1]]) := 3 * o(eta[2],muprime):
TodaName(x[2,[1,1,1]]) := o(eta[2],eta[3],eta[4]):
TodaName(x[3,[1,1,1]]) := 2 * nuprime:
TodaName(x[3,[2,1]]) := nuprime:
TodaName(x[4,[1,1,1]]) := 2 * E(nuprime):
TodaName(x[4,[2,1]]) := E(nuprime):
TodaName(x[2,[1,2,1]]) := 2 * o(eta[2],nuprime):
TodaName(x[3,[2,1,1]]) := o(nuprime,eta[6]):
TodaName(x[4,[2,1,1]]) := o(E(nuprime),eta[7]):
TodaName(x[4,[3,1]]) := o(nu[4],eta[7]):
TodaName(x[5,[3,1]]) := o(nu[5],eta[8]):
TodaName(x[2,[1,2,1,1]]) := o(eta[2],nuprime,eta[6]):
TodaName(x[3,[2,1,1,1]]) := o(nuprime,eta[6],eta[7]):
TodaName(x[4,[3,1,1]]) := o(nu[4],eta[7],eta[8]):
TodaName(x[4,[2,1,1,1]]) := o(E(nuprime),eta[7],eta[8]):
TodaName(x[5,[3,1,1]]) := o(nu[5],eta[8],eta[9]):
TodaName(x[6,[5,0]]) := w[6]:
TodaName(x[2,[1,2,1,1,1]]) := o(eta[2],nuprime,eta[6],eta[7]):
TodaName(x[4,[3,3]]) := o(nu[4],nu[7]):
TodaName(x[4,[3,2,1]]) := 2*o(nu[4],nu[7]):
TodaName(x[4,[3,1,1,1]]) := 4*o(nu[4],nu[7]):
TodaName(x[5,[4,1,1,1]]) := sigmathird:
TodaName(x[6,[5,1,1]]) := sigmasecond:
TodaName(x[6,[4,1,1,1]]) := 2*sigmasecond:
TodaName(x[7,[6,1]]) := sigmaprime:
TodaName(x[7,[5,1,1]]) := 2*sigmaprime:
TodaName(x[7,[4,1,1,1]]) := 4*sigmaprime:
TodaName(x[8,[6,1]]) := E(sigmaprime):
TodaName(x[8,[5,1,1]]) := 2*E(sigmaprime):
TodaName(x[8,[4,1,1,1]]) := 4*E(sigmaprime):
TodaName(x[6,[5,2,1]]) := 2*nubar[6]:
TodaName(x[6,[5,1,1,1]]) := 4*nubar[6]:
TodaName(x[7,[6,1,1]]) := o(sigmaprime,eta[14]):
TodaName(x[8,[6,1,1]]) := o(E(sigmaprime),eta[15]):
TodaName(x[8,[7,1]]) := o(sigma[8],eta[15]):
TodaName(x[9,[7,1]]) := o(sigma[9],eta[16]):
TodaName(x[7,[6,1,1,1]]) := o(sigmaprime,eta[14],eta[15]):
TodaName(x[8,[6,1,1,1]]) := o(E(sigmaprime),eta[15],eta[16]):
TodaName(x[8,[7,1,1]]) := o(sigma[8],eta[15],eta[16]):
TodaName(x[9,[7,1,1]]) := o(sigma[9],eta[16],eta[17]):
TodaName(x[2,[1,1,2,3,3]]) := o(eta[2],eta[3],epsilon[4]):
TodaName(x[3,[2,2,3,3]]) := epsilonprime:
TodaName(x[3,[1,1,2,3,3]]) := 2*epsilonprime:
TodaName(x[4,[2,2,3,3]]) := E(epsilonprime):
TodaName(x[4,[1,1,2,3,3]]) := 2*E(epsilonprime):
TodaName(x[4,[3,6,1]]) := o(nu[4],sigmaprime):
TodaName(x[4,[3,5,1,1]]) := 2*o(nu[4],sigmaprime):
TodaName(x[4,[3,4,1,1,1]]) := 4*o(nu[4],sigmaprime):
TodaName(x[5,[4,3,3]]) := o(nu[5],sigma[8]):
TodaName(x[5,[2,2,3,3]]) := 2*o(nu[5],sigma[8]):
TodaName(x[5,[1,1,2,3,3]]) := 4*o(nu[5],sigma[8]):
TodaName(x[6,[4,3,3]]) := o(nu[6],sigma[9]):
TodaName(x[6,[2,2,3,3]]) := 2*o(nu[6],sigma[9]):
TodaName(x[6,[1,1,2,3,3]]) := 4*o(nu[6],sigma[9]):
TodaName(x[7,[4,3,3]]) := o(nu[7],sigma[10]):
TodaName(x[7,[2,2,3,3]]) := 2*o(nu[7],sigma[10]):
TodaName(x[7,[1,1,2,3,3]]) := 4*o(nu[7],sigma[10]):
TodaName(x[8,[4,3,3]]) := o(nu[8],sigma[11]):
TodaName(x[8,[2,2,3,3]]) := 2*o(nu[8],sigma[11]):
TodaName(x[8,[1,1,2,3,3]]) := 4*o(nu[8],sigma[11]):
TodaName(x[8,[7,3]]) := o(sigma[8],nu[15]):
TodaName(x[8,[7,2,1]]) := 2*o(sigma[8],nu[15]):
TodaName(x[8,[7,1,1,1]]) := 4*o(sigma[8],nu[15]):
TodaName(x[9,[7,3]]) := o(sigma[9],nu[16]):
TodaName(x[9,[7,2,1]]) := 2*o(sigma[9],nu[16]):
TodaName(x[9,[7,1,1,1]]) := 4*o(sigma[9],nu[16]):
TodaName(x[10,[9,0]]) := w[10]:
TodaName(x[10,[7,3]]) := o(sigma[10],nu[17]):
TodaName(x[10,[7,2,1]]) := 2*o(sigma[10],nu[17]):
TodaName(x[11,[7,3]]) := o(sigma[11],nu[18]):
TodaName(x[2,[1,1,1,2,3,3]]) := 2*o(eta[2],epsilonprime):
TodaName(x[2,[1,1,2,4,1,1,1]]) := o(eta[2],eta[3],mu[4]):
TodaName(x[3,[2,2,4,1,1,1]]) := muprime:
TodaName(x[3,[1,1,2,4,1,1,1]]) := 2*muprime:
TodaName(x[3,[2,3,3,3]]) := o(epsilon[3],nu[11]):
TodaName(x[3,[2,1,2,3,3]]) := o(nuprime,epsilon[6]):
TodaName(x[4,[2,2,4,1,1,1]]) := E(muprime):
TodaName(x[4,[1,1,2,4,1,1,1]]) := 2*E(muprime):
TodaName(x[4,[2,3,3,3]]) := o(epsilon[4],nu[12]):
TodaName(x[4,[2,1,2,3,3]]) := o(E(nuprime),epsilon[7]):
TodaName(x[4,[3,6,1,1]]) := o(nu[4],sigmaprime,eta[14]):
TodaName(x[4,[3,5,3]]) := o(nu[4],nubar[7]):
TodaName(x[4,[3,2,3,3]]) := o(nu[4],epsilon[7]):
TodaName(x[5,[3,5,3]]) := o(nu[5],nubar[8]):
TodaName(x[5,[3,2,3,3]]) := o(nu[5],epsilon[8]):
TodaName(x[6,[5,3,3]]) := o(nubar[6],nu[14]):
TodaName(x[6,[3,2,3,3]]) := 2*o(nubar[6],nu[14]):
TodaName(x[7,[5,3,3]]) := o(nubar[7],nu[15]):
TodaName(x[8,[5,3,3]]) := o(nubar[8],nu[16]):
TodaName(x[9,[5,3,3]]) := o(nubar[9],nu[17]):


generators  :=  proc(G) 
 map(op,[op(G)]):
end:

for i from 0 to N do
 for j from 1 to i+2 do
  G  :=  SpherePi(i+j,j):
  for a in generators(G) do
   if not(Source(a)=i+j and
          Target(a)=j and
          IsAdmissible(a)) then
    print([i+j,j,a]):
   fi:
  od:
 od:
od:

all_gens  :=  [seq(seq(op(generators(SpherePi(i,j))),i=1..j+N),j=1..N+2)]:

for a in all_gens do
 GN(TodaName(a)) := a:
od:

for a in all_gens do
 m := Source(a):
 n := Target(a):
 b := two(a):
 if type(b,specfunc(anything,two)) then
  two(a) := 0:
 fi:
 b := E(a):
 if type(b,specfunc(anything,E)) then
  E(a) := x[op(1,a)+1,op(2,a)]:
 fi:
 b := H(a):
 if type(b,specfunc(anything,H)) then
  if (2*m-1>n or n=m) then 
   H(a) := 0:
  else
   J := op(2,a):
   if J[1] > n-1 then
    H(a) := 0:
   else 
    H(a) := x[2*n-1,J[2..-1]]:
   fi:
  fi:
 fi:

 o(a,x[m,[]]) := a;
 o(x[n,[]],a) := a;
od:

for n in degrees_above(5) do
 two(x[n,[3]]) := x[n,[2,1]]:
 two(x[n,[2,1]]) := x[n,[1,1,1]]:
 two(x[n,[4,4,1,1,1]]) := x[n,[2,2,4,1,1,1]]:
 two(x[n,[2,2,4,1,1,1]]) := x[n,[1,1,2,4,1,1,1]]:
od:

for n in degrees_above(6) do
 two(x[n,[5,1,1]])       := x[n,[4,1,1,1]]:
od:

for n in degrees_above(9) do 
 two(x[n,[7]]) := x[n,[6,1]]:
 two(x[n,[6,1]]) := x[n,[5,1,1]]:
 two(x[n,[5,1,1]]) := x[n,[4,1,1,1]]:
od:

two(x[2,[1]])           := x[2,[1,0]]:
two(x[2,[1,1,1,1]])     := x[2,[1,2,1]]:
two(x[2,[1,1,1,1]])     := x[2,[1,2,1]]:
two(x[2,[1,2,2,3,3]])   := x[2,[1,1,1,2,3,3]]:
two(x[3,[2,1]])         := x[3,[1,1,1]]:
two(x[4,[3]])           := x[4,[3,0]]:
two(x[4,[3,2,1]])       := x[4,[3,1,1,1]]:
two(x[4,[3,3]])         := x[4,[3,2,1]]:
two(x[4,[3,6,1]])       := x[4,[3,5,1,1]]:
two(x[5,[2,2,3,3]])     := x[5,[1,1,2,3,3]]:
two(x[5,[3,5,1,1]])     := x[5,[3,4,1,1,1]]:
two(x[5,[4,3,3]])       := x[5,[2,2,3,3]]:
two(x[6,[2,2,3,3]])     := x[6,[1,1,2,3,3]]:
two(x[6,[4,3,3]])       := x[6,[2,2,3,3]]:
two(x[6,[5,1,1]])       := x[6,[4,1,1,1]]:
two(x[6,[5,2,1]])       := x[6,[5,1,1,1]]:
two(x[6,[5,3,3]])       := x[6,[3,2,3,3]]:
two(x[6,[5,3]])         := x[6,[5,2,1]]:
two(x[7,[2,2,3,3]])     := x[7,[1,1,2,3,3]]:
two(x[7,[4,3,3]])       := x[7,[2,2,3,3]]:
two(x[7,[5,1,1,1]])     := x[7,[4,1,1,1,1]]:
two(x[7,[6,1]])         := x[7,[5,1,1]]:
two(x[8,[2,2,3,3]])     := x[8,[1,1,2,3,3]]:
two(x[8,[4,3,3]])       := x[8,[2,2,3,3]]:
two(x[8,[5,1,1,1]])     := x[8,[4,1,1,1,1]]:
two(x[8,[6,1]])         := x[8,[5,1,1]]:
two(x[8,[7]])           := x[8,[7,0]]:
two(x[8,[7,2,1]])       := x[8,[7,1,1,1]]:
two(x[8,[7,3]])         := x[8,[7,2,1]]:
two(x[9,[7,2,1]])       := x[9,[7,1,1,1]]:
two(x[9,[7,3]])         := x[9,[7,2,1]]:
two(x[10,[7,3]])        := x[10,[7,2,1]]:

for n in degrees_above(2) do 
 o(x[n,[1]],x[n+1,[1]]) := x[n,[1,1]]:
 o(x[n,[1]],x[n+1,[1,1]]) := x[n,[1,1,1]]:
 o(x[n,[1,1]],x[n+2,[1]]) := x[n,[1,1,1]]:
 o(x[n,[1]],x[n+1,[2,3,3]]) := x[n,[1,2,3,3]]:
 o(x[n,[1]],x[n+1,[2,4,1,1,1]]) := x[n,[1,2,4,1,1,1]]:
od:

for n in degrees_above(4) do
 o(x[n,[3]],x[n+3,[3]]) := x[n,[3,3]]:
 o(x[n,[3]],x[n+3,[3,3]]) := x[n,[3,3,3]]:
 o(x[n,[3,3]],x[n+6,[3]]) := x[n,[3,3,3]]:
od:

# Predictable ternary+ composites
o(x[2,[1]],    x[3,[2,1]],   x[6,[1]],   x[7,[1]]) := x[2,[1,2,1,1,1]]:
o(x[3,[2,1]],  x[6,[1]],     x[7,[1]])             := x[3,[2,1,1,1]]:
o(x[4,[2,1]],  x[7,[1]],     x[8,[1]])             := x[4,[2,1,1,1]]:
o(x[4,[3]],    x[7,[1]],     x[8,[1]])             := x[4,[3,1,1]]:
o(x[4,[3]],    x[7,[6,1]],   x[14,[1]])            := x[4,[3,6,1,1]]:
o(x[4,[3]],    x[7,[3]],     x[10,[3]])            := x[4,[3,3,3]]:
o(x[5,[3]],    x[8,[1]],     x[9,[1]])             := x[5,[3,1,1]]:
o(x[7,[6,1]],  x[14,[1]],    x[15,[1]])            := x[7,[6,1,1,1]]:
o(x[8,[6,1]],  x[15,[1]],    x[16,[1]])            := x[8,[6,1,1,1]]:
o(x[8,[7]],    x[15,[1]],    x[16,[1]])            := x[8,[7,1,1]]:
o(x[9,[7]],    x[16,[1]],    x[17,[1]])            := x[9,[7,1,1]]:

# Predictable composites
o(x[2,[1]],    x[3,[1,2,3,3]])     := x[2,[1,1,2,3,3]]:
o(x[2,[1]],    x[3,[1,1,2,3,3]])   := x[2,[1,1,1,2,3,3]]:
o(x[2,[1]],    x[3,[1,2,4,1,1,1]]) := x[2,[1,1,2,4,1,1,1]]:
o(x[2,[1]],    x[3,[2,1]])         := x[2,[1,2,1]]:
o(x[2,[1]],    x[3,[2,1,1]])       := x[2,[1,2,1,1]]:
o(x[2,[1]],    x[3,[2,1,1,1]])     := x[2,[1,2,1,1,1]]:
o(x[2,[1]],    x[3,[1,1,1]])       := x[2,[1,1,1,1]]:
o(x[2,[1,1]],  x[4,[2,1]])         := 0:
o(x[2,[1,1]],  x[4,[1,1]])         := x[2,[1,1,1,1]]: #?
o(x[2,[1,1,1]],x[5,[1]])           := x[2,[1,1,1,1]]:
o(x[2,[1]],    x[3,[2,1]])         := x[2,[1,2,1]]:
o(x[2,[1,2,1]],x[6,1])             := x[2,[1,2,1,1]]:
o(x[3,[1]],    x[4,[2,1]])         := 0:
o(x[3,[1]],    x[4,[2,1,1]])       := 0:
o(x[3,[1]],    x[4,[2,4,1,1,1]])   := x[3,[1,2,4,1,1,1]]:
o(x[3,[2,1]],  x[6,[1]])           := x[3,[2,1,1]]:
o(x[3,[2,1]],  x[6,[1,1]])         := x[3,[2,1,1,1]]:
o(x[3,[2,1,1]],x[7,[1]])           := x[3,[2,1,1,1]]:
o(x[3,[2,1]],  x[6,[2,3,3]])       := x[3,[2,1,2,3,3]]:
o(x[3,[2,3,3]],x[11,[3]])          := x[3,[2,3,3,3]]:
o(x[4,[2,1]],  x[7,[1]])           := x[4,[2,1,1]]:
o(x[4,[2,1]],  x[7,[2,3,3]])       := x[4,[2,1,2,3,3]]:
o(x[4,[2,3,3]],x[12,[3]])          := x[4,[2,3,3,3]]:
o(x[4,[3]],    x[7,[1]])           := x[4,[3,1]]:
o(x[4,[3]],    x[7,[2,3,3]])       := x[4,[3,2,3,3]]:
o(x[4,[3]],    x[7,[3]])           := x[4,[3,3]]:
o(x[4,[3]],    x[7,[5,3]])         := x[4,[3,5,3]]:
o(x[4,[3]],    x[7,[6,1]])         := x[4,[3,6,1]]:
o(x[5,[3]],    x[8,[1]])           := x[5,[3,1]]:
o(x[5,[3]],    x[8,[2,3,3]])       := x[5,[3,2,3,3]]:
o(x[5,[3]],    x[8,[5,3]])         := x[5,[3,5,3]]:
o(x[6,[5,3]],  x[14,[3]])          := x[6,[5,3,3]]:
o(x[7,[5,3]],  x[15,[3]])          := x[7,[5,3,3]]:
o(x[7,[6,1]],  x[14,[1]])          := x[7,[6,1,1]]:
o(x[8,[5,3]],  x[16,[3]])          := x[8,[5,3,3]]:
o(x[8,[6,1]],  x[15,[1]])          := x[8,[6,1,1]]:
o(x[8,[7]],    x[15,[1]])          := x[8,[7,1]]:
o(x[8,[7]],    x[15,[3]])          := x[8,[7,3]]:
o(x[9,[5,3]],  x[17,[3]])          := x[9,[5,3,3]]:
o(x[9,[7]],    x[16,[1]])          := x[9,[7,1]]:
o(x[9,[7]],    x[16,[3]])          := x[9,[7,3]]:
o(x[10,[7]],   x[17,[3]])          := x[10,[7,3]]:
o(x[11,[7]],   x[18,[3]])          := x[11,[7,3]]:
o(x[2,[1,1]],  x[4,[1]])           := x[2,[1,1,1]]:
o(x[2,[1,1]],  x[4,[2,3,3]])       := x[2,[1,1,2,3,3]]:

o(x[2, [1, 1]], x[4, [2, 4, 1, 1, 1]]) := x[2, [1, 1, 2, 4, 1, 1, 1]]:
o(x[2, [1, 1]], x[4, [2, 1, 1]]) := 0:
o(x[2, [1, 2, 1, 1]], x[7, [1]]) := x[2, [1, 2, 1, 1, 1]]:

# Unpredictable composites
o(x[2,[1]],    x[3,[2,1]])   := x[2,[1,1,1,1]] + x[2,[1,2,1]]:
o(x[2,[1]],    x[3,[2,2,3,3]]) := x[2,[1,2,2,3,3]]+x[2,[1,1,1,2,3,3]]:
o(x[5,[3]],    x[8,[7]])     := x[5,[4,3,3]]:
o(x[6,[3]],    x[9,[7]])     := x[6,[4,3,3]]:
o(x[7,[3]],    x[10,[7]])    := x[7,[4,3,3]]:
o(x[8,[3]],    x[11,[7]])    := x[8,[4,3,3]]:

# Suspensions
E(x[2,[1,1,1,1]]) := 0:
E(x[2,[1,2,1]])   := 0:

# (************************************************************************)
# (* Suspensions                                                          *)




# TodaName(x[6,[5,0]])               := w[6]:
# TodaName(x[6,[5,1,1]])             := sigmasecond:
# TodaName(x[7,[6,1]])               := sigmaprime:
# TodaName(x[8,[6,1]])               := E(sigmaprime):
# TodaName(x[10,[9,0]])              := w[10]:

# TodaName(x[2,[1,1,1,2,3,3]])       := 2*o(x[2,[1]],x[3,[2,2,3,3]]):
# TodaName(x[2,[1,2,1]])             := 2*o(x[2,[1]],x[3,[2,1]]):
# TodaName(x[3,[1,1,1]])             := 2*x[3,[2,1]]:
# TodaName(x[3,[1,1,2,3,3]])         := 2*x[3,[2,2,3,3]]:
# TodaName(x[3,[1,1,2,4,1,1,1]])     := 2*x[3,[2,2,4,1,1,1]]:
# TodaName(x[4,[1,1,1]])             := 2*x[4,[2,1]]:
# TodaName(x[4,[1,1,2,3,3]])         := 2*x[4,[2,2,3,3]]:
# TodaName(x[4,[1,1,2,4,1,1,1]])     := 2*x[4,[2,2,4,1,1,1]]:
# TodaName(x[4,[3,2,1]])             := 2*o(x[4,[3]],x[7,[3]]):
# TodaName(x[4,[3,5,1,1]])           := 2*o(x[4,[3]],x[7,[6,1]]):
# TodaName(x[5,[2,2,3,3]])           := 2*o(x[5,[3]],x[8,[7]]):
# TodaName(x[6,[2,2,3,3]])           := 2*o(x[6,[3]],x[9,[7]]):
# TodaName(x[6,[3,2,3,3]])           := 2*o([6,[5,3]],x[14,[3]]):
# TodaName(x[6,[4,1,1,1]])           := 2*x[6,[5,1,1]]:
# TodaName(x[6,[5,2,1]])             := 2*[6,[5,3]]:
# TodaName(x[7,[2,2,3,3]])           := 2*o(x[7,[3]],x[10,[7]]):
# TodaName(x[7,[5,1,1]])             := 2*x[7,[6,1]]:
# TodaName(x[8,[2,2,3,3]])           := 2*o(x[8,[3]],x[11,[7]]):
# TodaName(x[8,[5,1,1]])             := 2*x[8,[6,1]]:
# TodaName(x[8,[7,2,1]])             := 2*o(x[8,[7]],x[15,[3]]):
# TodaName(x[9,[7,2,1]])             := 2*o(x[9,[7]],x[16,[3]]):
# TodaName(x[10,[7,2,1]])            := 2*o(x[10,[7]],x[17,[3]]):

# TodaName(x[4,[3,1,1,1]])           := 4*o(x[4,[3]],x[7,[3]]):
# TodaName(x[4,[3,4,1,1,1]])         := 4*o(x[4,[3]],x[7,[6,1]]):
# TodaName(x[5,[1,1,2,3,3]])         := 4*o(x[5,[3]],x[8,[7]]):
# TodaName(x[6,[1,1,2,3,3]])         := 4*o(x[6,[3]],x[9,[7]]):
# TodaName(x[6,[5,1,1,1]])           := 4*[6,[5,3]]:
# TodaName(x[7,[1,1,2,3,3]])         := 4*o(x[7,[3]],x[10,[7]]):
# TodaName(x[7,[4,1,1,1]])           := 4*x[7,[6,1]]:
# TodaName(x[8,[1,1,2,3,3]])         := 4*o(x[8,[3]],x[11,[7]]):
# TodaName(x[8,[4,1,1,1]])           := 4*x[8,[6,1]]:
# TodaName(x[8,[7,1,1,1]])           := 4*o(x[8,[7]],x[15,[3]]):
# TodaName(x[9,[7,1,1,1]])           := 4*o(x[9,[7]],x[16,[3]]):


# TodaName(x[2,[1,1,1,1]])           := - o(x[2,[1]],x[3,[2,1]]):
# TodaName(x[2,[1,2,2,3,3]])         := 3 * o(x[2,[1]],x[3,[2,2,3,3]]):
# TodaName(x[2,[1,2,2,4,1,1,1]])     := 3 * o(x[2,[1]],x[3,[2,2,4,1,1,1]]):

# TodaName(x[2,[1,1,2,3,3]])         := o(x[2,[1]],x[3,[1]],x[4,[2,3,3]]):
# TodaName(x[2,[1,1,2,4,1,1,1]])     := o(x[2,[1]],x[3,[1]],x[4,[2,4,1,1,1]]):
# TodaName(x[2,[1,2,1,1,1]])         := o(x[2,[1]],x[3,[2,1]],x[6,[1]],x[7,[1]]):
# TodaName(x[2,[1,2,1,1]])           := o(x[2,[1]],x[3,[2,1]],x[6,[1]]):
# TodaName(x[3,[2,1,1,1]])           := o(x[3,[2,1]],x[6,[1]],x[7,[1]]):
# TodaName(x[4,[2,1,1,1]])           := o(x[4,[2,1]],x[7,[1]],x[8,[1]]):
# TodaName(x[4,[3,1,1]])             := o(x[4,[3]],x[7,[1]],x[8,[1]]):
# TodaName(x[4,[3,6,1,1]])           := o(x[4,[3]],x[7,[6,1]],x[14,[1]]):
# TodaName(x[7,[6,1,1,1]])           := o(x[7,[6,1]],x[14,[1]],x[15,[1]]):
# TodaName(x[8,[6,1,1,1]])           := o(x[8,[6,1]],x[15,[1]],x[16,[1]]):
# TodaName(x[8,[7,1,1]])             := o(x[8,[7]],x[15,[1]],x[16,[1]]):
# TodaName(x[9,[7,1,1]])             := o(x[9,[7]],x[16,[1]],x[17,[1]]):
# TodaName(x[5,[3,1,1]])             := o(x[5,[3]],x[8,[1]],x[9,[1]]):


