#@ Not autoload

N := 20;

Families  := []:
Elements  := []:
Relations := []:

ElementDocumentation := "":

LaTeXName     := table([]):

FamilyStem := proc(u)
 'FamilyStem'(u);
end:

FamilySource := proc(u)
 'FamilySource'(u);
end:

FamilyTarget := proc(u)
 'FamilyTarget'(u);
end:

Source        := proc(u)
 local L;
 if type(u,integer) then
  return(0);
 elif type(u,`+`) then
  L := map(Source,{op(u)});
  if nops(L) = 1 then
   return(L[1]);
  else
   return(FAIL);
  fi;
 elif type(u,specfunc(anything,o)) then
  return(Source(op(-1,o)));
 elif type(u,specfunc(anything,E)) then
  return(Source(op(1,u))+1);
 elif type(u,specfunc(anything,H)) then
  return(Source(op(1,u)));
 elif type(u,specfunc(anything,P)) then
  return(Source(op(1,u))-2);
 elif type(u,indexed) and type(FamilyStem(op(0,u)),integer) then
  return(FamilyStem(op(0,u))+op(1,u));
 else
  return('Source'(args));
 fi;
end:

Target        := proc(u)
 local L;
 if type(u,integer) then
  return(0);
 elif type(u,`+`) then
  L := map(Target,{op(u)});
  if nops(L) = 1 then
   return(L[1]);
  else
   return(FAIL);
  fi;
 elif type(u,specfunc(anything,o)) then
  return(Target(op(1,o)));
 elif type(u,specfunc(anything,E)) then
  return(Target(op(1,u))+1);
 elif type(u,specfunc(anything,H)) then
  return(2*Target(op(1,u))-1);
 elif type(u,specfunc(anything,P)) then
  return((Target(op(1,u))-1)/2);
 elif type(u,indexed) and type(FamilyStem(op(0,u)),integer) then
  return(op(1,u));
 else
  return('Target'(args));
 fi;
end:

E := proc(u) 
 if type(u,`+`) then
  return(map(E,u));
 elif type(u,specfunc(anything,o)) then
  return(map(E,u));
 elif type(u,specfunc(anything,P)) then
  return(0);
 elif type(u,indexed) and member(op(0,u),Families) and nops(u) > 0 then
  return(op(0,u)[op(1,u)+1]);
 else
  return('E'(args));
 fi;
end:

H := proc(u) 
 if type(u,`+`) then
  return(map(H,u));
 elif type(u,specfunc(anything,E)) then
  return(0);
 else
  return('H'(args));
 fi;
end:

P := proc(u) 
 if type(u,`+`) then
  return(map(P,u));
 elif type(u,specfunc(anything,H)) then
  return(0);
 else
  return('P'(args));
 fi;
end:

is_E := proc(u)
 if type(u,specfunc(anything,E)) then
  return true;
 elif type(u,indexed) and
      member(op(0,u),Families) and
      op(1,u) > FamilyTarget(op(0,u)) then
  return true;
 else
  return false;
 fi;
end:

o := proc(a,b)
 local a0,a1,b0,b1;
 if a=0 or b=0 then
  return(0);
 elif type(b,`+`) then
  return(map2(o,a,b));
 elif type(b,`*`) then
  b0,b1 := selectremove(type,b,integer);
  return b0 * o(a,b1);
 elif type(a,`+`) and is_E(b) then
  return(map(o,a,b));
 elif type(a,`*`) and is_E(b) then
  a0,a1 := selectremove(type,a,integer);
  return a0 * o(a1,b);
 else
  return('o'(args));
 fi;
end:

Definition    := table([]):
Indeterminacy := table([]):
AdditiveOrder := table([]):

LaTeXForm :=
 proc(x)
  local s;
  s := LaTeXName[x];
  if not(type([s],[string])) then s := sprintf("%A",x); fi;
  s;
 end:

DeclareFamily := 
 proc(nam,fmt,source,target,defn)
  global Families,LaTeXName,Source,Target,Definition,ElementDocumentation;
  Families := [op(Families),nam];
  LaTeXName[nam]  := fmt;
  FamilySource(nam)     := source;
  FamilyTarget(nam)     := target;
  FamilyStem(nam)       := source-target;
  Definition[nam] := defn;
  ElementDocumentation := 
   cat(
    ElementDocumentation,
    "\n\\item ",defn,
    " Maple notation is {\\tt ",convert(nam,string),"[n]}.\n"
   );
 end:
 
DeclareElement := 
 proc(nam,fmt,source,target,defn)
  global Elements,LaTeXName,Source,Target,Definition,ElementDocumentation;
  Elements := [op(Elements),nam];
  LaTeXName[nam]  := fmt;
  Source(nam)     := source;
  Target(nam)     := target;
  Definition[nam] := defn;
  ElementDocumentation := 
   cat(
    ElementDocumentation,
    "\n\\item ",defn,
    " Maple notation is {\\tt ",convert(nam,string),"[n]}.\n"
   );
 end:

SetOrder := 
 proc(x,n::Or(posint,identical(infinity)),reason::string)
  global AdditiveOrder;
  AdditiveOrder[x] := n;
 end:

Relations := [];
FullRelations := [];

AddRelation := 
 proc(a,cond,b,text)
  global Relations,FullRelations;
  local var,v0,a0,b0;

  FullRelations := [op(FullRelations),[a,cond,b,text]];
  if type(cond,`<=`) then
   var := rhs(cond);
   v0 := lhs(cond);
   a0 := subs(var = v0,a);
   b0 := subs(var = v0,b);
   while (Source(a0) <= 2*N and Target(v0) <= N and v0 <= 3*N) do
    Relations := [op(Relations),a0 = b0];
    v0 := v0+1;
    a0 := subs(var = v0,a);
    b0 := subs(var = v0,b);
   od:
  else
   Relations := [op(Relations),a = b];
  fi;
 end:
 
######################################################################

# Declarations of elements and families of elements                   

DeclareFamily(
 iota,"\\iota",1,1,
 "\\(\\iota_n:S^n\\rightarrow S^n\\) is the identity map."
):

Indeterminacy[iota[1]] := {}:

DeclareFamily(
 eta,"\\eta",3,2,
 cat(
  "\\(\\eta_2:S^3\\rightarrow S^2\\) is the complex Hopf map.  ",
  "For \\(k\\geq 2\\) we put \\(\\eta_k=\\E^{k-2}\\eta_2\\). "
 )
):

Indeterminacy[eta[2]] := {}:

DeclareFamily(
 nu,"\\nu",7,4,
 cat( 
  "\\(\\nu_4:S^7\\rightarrow S^4\\) is defined by the properties ",
  "\\(H(\\nu_4)=\\iota_7\\) and \\(2\\E(\\nu_4)=\\E^2\\nu'\\) ",
  "(Lemma 5.4).  I think this only defines it modulo \\(2\\nu'\\).  ",
  "However, I think we pin it down precisely by requiring that ",
  "\\(\\nu_4\\) should be equal to the quaternionic Hopf map plus an ",
  "odd torsion class, and that \\(\\E\\nu_4\\) should be 2-torsion. ",
  "For \\(n\\geq 4\\) we put \\(\\nu_n=\\E^{n-4}\\nu_4\\)."
 )
):

Indeterminacy[nu[4]] := {}:

DeclareFamily(
 sigma,"\\sigma",15,8,
 cat(
  "\\(\\sigma_8:S^{15}\\rightarrow S^{8}\\) is the octonionic Hopf map ",
  "plus an odd torsion class, chosen so that \\(\\E\\sigma_8\\) is ",
  "2-torsion.  Toda defines it (Lemma 5.14) by the property that ",
  "\\(H(\\sigma_8)=\\iota_{15}\\). ",
  "For \\(n\\geq 8\\) we put \\(\\sigma_n=\\E^{n-8}\\sigma_8\\)."
 )
):

Indeterminacy[sigma[8]] := {}:

DeclareFamily(
 epsilon,"\\epsilon",11,3,
 cat(
  "\\(\\epsilon_3:S^{11}\\rightarrow S^3\\) is the unique element of the ",
  "Toda bracket \\(\\langle\\eta_3,\\E\\nu',\\nu_7\\rangle_1\\) (see ",
  "the beginning of Toda's Chapter VI). ",
  "For \\(k\\geq 3\\) we put \\(\\epsilon_k=\\E^{k-3}\\epsilon_3\\)."
 )
):

TodaBracketRepresentation[epsilon[3]] := 
 TodaBracket[{eta[3],nuprime,nu[6]},1]:
Indeterminacy[epsilon[3]] := {}:

DeclareFamily(
 nubar,"\\overline{\\nu}",14,6,
 cat(
  "In Toda's Section VI(ii) he defines \\(\\nubar_6:S^{14}\\rightarrow S^6\\) ",
  "to be an element of the Toda bracket ",
  "\\(\\langle\\nu_6,\\eta_9,\\nu_{10}\\rangle_1\\).  We will let \\(\\nubar_6\\)",
  "denote the unique element of this Toda bracket that satisfies ",
  "\\(H(\\nubar_6)=\\nu_{11}\\).  This definition is validated in ",
  "the notes by Strickland. ",
  "We put \\(\\nubar_n=\\E^{n-6}\\nubar_6\\) for \\(n\\geq 6\\)."
 )
):

TodaBracketRepresentation[nubar[6]] := 
 TodaBracket[{nu[6],eta[8],nu[9]},1]:
Indeterminacy[nubar[6]] := {}:

DeclareFamily(
 mu,"\\mu",12,3,
 cat(
  "The map \\(\\mu_3:S^{12}\\rightarrow S^3\\) is defined in Toda's ",
  "Section VI(iii) by a procedure of several steps, involving the cofibre ",
  "of the map \\(\\nu':S^6/8\\rightarrow S^3\\).  It turns out that the ",
  "indeterminacy is \\(\\{0,\\eta_3\\circ\\epsilon_4\\}\\) ",
  "(see the discussion preceeding Lemma 6.5, together with Theorem 7.1). ",
  "We also have ",
  "\\(\\pi_{12}S^3=\\Z_2\\mu_3\\oplus\\Z_2(\\eta_3\\circ\\epsilon_4)\\). ",
  "The element \\(\\eta_3\\circ\\epsilon_4\\) has Adams filtration 4, ",
  "and we make the unique choice of \\(\\mu_3\\) that has Adams ",
  "filtration 5. ",
  "We write \\(\\mu_k=\\E^{k-3}\\mu_3\\) for \\(k\\geq 3\\). "
 )
):

Indeterminacy[mu[3]] := {}:

DeclareFamily(
 zeta,"\\zeta",16,5,
 cat(
  "We define \\(\\zeta_5:S^{16}\\rightarrow S^5\\) to be the unique element ",
  "of the Toda bracket ",
  "\\(\\langle\\nu_5,8\\iota_8,\\E\\sigma'\\rangle_1\\) that satisfies ",
  "\\(H(\\zeta_5)=8\\sigma_9\\) and \\(P(\\zeta_5)=\\pm\\eta_2\\circ\\mu'\\). ",
  "This is validated in the notes by Strickland, based on Toda's Section VI(v). ",
  "For \\(k\\geq 5\\) we put \\(\\zeta_k=\\E^{k-5}\\zeta_5\\). "
 )
):

TodaBracketRepresentation[zeta[5]] := 
 TodaBracket[{nu[5],8 * iota[7],sigmaprime},1]:
Indeterminacy[zeta[5]] := {}:

DeclareFamily(
 kappa,"\\kappa",21,7,
 cat(
  "The element \\(\\kappa_7:S^{21}\\rightarrow S^7\\) is defined in Toda's ",
  "Section X(i) as an element of a Toda bracket involving the Moore space ",
  "\\(S^9/2\\).  The indeterminacy is not given explicitly.  For \\(k\\geq 7\\) ",
  "we put \\(\\kappa_k=\\E^{k-7}\\kappa_7\\)."
 )
):

DeclareFamily(
 epsilonbar,"\\overline{\\epsilon}",18,3,
 cat(
  "\\(\\epsilonbar_3:S^{18}\\rightarrow S^3\\) is the unique element of the Toda ",
  "bracket \\(\\langle \\epsilon_3,2\\iota_{5},\\nu_5\\circ\\nu_8\\rangle_6\\), ",
  "and the unique nonzero element of \\(\\pi_{18}^3\\).  See Toda's Section X(i) ",
  "and Theorem 10.5.  For \\(k\\geq 3\\) we put ",
  "\\(\\epsilonbar_k=\\E^{k-3}\\epsilonbar_3\\). "
 )
):

TodaBracketRepresentation[epsilonbar[3]] := 
 TodaBracket[{epsilon[3],2 * iota[5],o[nu[5],nu[8]]},6]:
Indeterminacy[epsilonbar[3]] := {}:

DeclareFamily(
 rho,"\\rho",28,13,
 cat(
  "\\(\\rho_{13}:S^{28}\\rightarrow S^{13}\\) is defined in Toda's Lemma 10.9 ",
  "by the properties \\(2\\rho_{13}=\\E^4\\rho'\\) and ",
  "\\(\\E^{\\infty}\\rho_{13}\\in\\langle\\sigma,2\\sigma,8\\iota\\rangle\\). ",
  "For \\(k\\geq 13\\) we put \\(\\rho_k=\\E^{k-13}\\rho_{13}\\)."
 )
):

DeclareFamily(
 zetabar,"\\overline{\\zeta}",24,5,
 cat(
  "\\(\\zetabar_5:S^{24}\\rightarrow S^5\\) is an element of the Toda bracket ",
  "\\(\\langle\\zeta_5,8\\iota_{16},2\\sigma_{16}\\rangle_1\\). ",
  "See the preamble to Toda's Lemma 12.4. ",
  "For \\(k\\geq 5\\) we put \\(\\zetabar_k=\\E^{k-5}\\zetabar_5\\)."
 )
):

TodaBracketRepresentation[zetabar[5]] := 
 TodaBracket[{zeta[5],8 * iota[15],2 * sigma[15]},1]:

DeclareFamily(
 sigmabar,"\\overline{\\sigma}",25,6,
 cat(
  "\\(\\sigmabar_6:S^{25}\\rightarrow S^6\\) is an element of the Toda ",
  "bracket \\(\\langle\\nu_6,\\epsilon_9+\\nubar_9,\\sigma_{16}\\rangle_1\\). ",
  "See the preamble to Toda's Lemma 12.5. ",
  "For \\(k\\geq 6\\) we put \\(\\sigmabar_k=\\E^{k-6}\\sigmabar_6\\)."
 )
):

TodaBracketRepresentation[sigmabar[6]] := 
 TodaBracket[{nu[6],epsilon[8] + nubar[8],sigma[15]},1]:

DeclareFamily(
 omega,"\\omega",30,14,
 cat(
  "\\(\\omega_{14}:S^{30}\\rightarrow S^{14}\\) is defined in ",
  "Toda's Lemma 12.15(i) by the requirement that ",
  "\\(H(\\omega_{14})=\\nu_{27}\\).  The indeterminacy is ",
  "\\(\\{0,\\sigma_{14}\\circ\\mu_{21}\\}\\). ",
  "For \\(k\\geq 14\\) we put \\(\\omega_k=\\E^{k-14}\\omega_{14}\\)."
 )
):

Indeterminacy[omega[14]] := {o[sigma[14],mu[21]]}:

DeclareFamily(
 etastar,"\\eta^*",32,16,
 cat(
  "\\(\\eta_{16}^{*}:S^{32}\\rightarrow S^{16}\\) is an element of the ",
  "Toda bracket ",
  "\\(\\langle\\sigma_{16},2\\sigma_{23},\\eta_{30}\\rangle_1\\). ",
  "See Toda's Section XII(iii). ",
  "For \\(k\\geq 16\\) we put \\(\\eta_{k}^{*}=\\E^{k-16}\\eta_{16}^{*}\\).  ",
  "For \\(k\\geq 18\\) we have \\(\\eta_{k}^{*}=\\omega_{k}\\) modulo ",
  "\\({\\sigma_{k}}\\circ{\\mu_{k+7}}\\), so either \\(\\eta_{k}^{*}\\) or ",
  "\\(\\omega_{k}\\) can be used as a generator of \\(\\pi_{k+16}^{k}\\)."
 )
):

TodaBracketRepresentation[etastar[16]] := 
 TodaBracket[{sigma[16],2 * sigma[22],eta[29]},1]:

DeclareFamily(
 epsilonstar,"\\epsilon^*",29,12,
 cat(
  "\\(\\epsilon_{12}^{*}:S^{29}\\rightarrow S^{12}\\) is defined in Toda's ",
  "Lemma 12.15(ii) by the properties ",
  "\\(H(\\epsilon_{12}^{*})=\\nu_{23}\\circ\\nu_{27}\\) and ",
  "\\(\\E^2\\epsilon_{12}^{*}=\\omega_{14}\\circ\\eta_{30}\\). ",
  "This fixes \\(\\epsilon_{12}^{*}\\) as a function of ",
  "\\(\\omega_{14}\\).  However, the indeterminacy of ",
  "\\(\\sigma_{14}\\circ\\mu_{21}\\) in \\(\\omega_{14}\\) creates an indeterminacy ",
  "of \\(\\sigma_{12}\\circ\\eta_{19}\\circ\\mu_{20}\\) in \\(\\epsilon_{12}^{*}\\). ",
  "For \\(k\\geq 12\\) we put \\(\\epsilon_{k}^{*}=\\E^{k-12}\\epsilon^{*}_{12}\\)."
 )
):

DeclareFamily(
 mubar,"\\overline{\\mu}",20,3,
 cat(
  "\\(\\mubar_3:S^{20}\\rightarrow S^3\\) is defined in the preamble to ",
  "Toda's Lemma 12.2 to be an element of the Toda bracket ",
  "\\(\\langle\\mu_3,2\\iota_{12},8\\sigma_{12}\\rangle_1\\). ",
  "I have not checked the indeterminacy. ",
  "For \\(k\\geq 3\\) we put \\(\\mubar_{k}=\\E^{k-3}\\mubar_3\\). "
 )
):

TodaBracketRepresentation[mubar[3]] := 
 TodaBracket[{mu[3],2 * iota[11],8 * sigma[11]},1]:

DeclareFamily(
 nustar,"\\nu^*",34,16,
 cat(
  "\\(\\nu^*_{16}:S^{34}\\rightarrow S^{16}\\) is defined in Toda's ",
  "Section XII(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma_{16},2\\sigma_{23},\\nu_{30}\\rangle_1\\).  ",
  "I have not checked the indeterminacy. ",
  "For \\(k\\geq 16\\) we put \\(\\nu^*_{k}=\\E^{k-16}\\nu^*_{16}\\). "
 )
):

TodaBracketRepresentation[nustar[16]] := 
 TodaBracket[{sigma[16],2 * sigma[22],nu[29]},1]:

DeclareFamily(
 xi,"\\xi",30,12,
 cat(
  "\\(\\xi_{12}:S^{30}\\rightarrow S^{12}\\) is defined in Toda's ",
  "Section XII(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma_{12},\\nu_{19},\\sigma_{22}\\rangle_1\\).  ",
  "I have not checked the indeterminacy. ",
  "For \\(k\\geq 12\\) we put \\(\\xi_{k}=\\E^{k-12}\\xi_{16}\\). "
 )
):

TodaBracketRepresentation[xi[12]] := 
 TodaBracket[{sigma[12],nu[18],sigma[21]},1]:

DeclareElement(
 nuprime,"\\nu'",6,3,
 cat(
  "\\(\\nu'\\) is an element of the Toda bracket ",
  "\\(\\langle\\nu_3,2\\iota_4,\\eta_4\\rangle_1\\).  I think it is also ",
  "obtained by applying the unstable J-homomorphism to the generator of ",
  "\\(\\pi_3SO(3)\\).  Toda's definition is indeterminate up to sign. ",
  "See Toda's Equations 5.3 and 5.4. "
 )
):

TodaBracketRepresentation[nuprime] := 
 TodaBracket[{eta[3],2 * iota[3],eta[3]},1]:
Indeterminacy[nuprime] := {2 * nuprime}:

DeclareElement(
 sigmathird,"\\sigma'''",12,5,
 cat(
  "\\(\\sigma''':S^{12}\\rightarrow S^5\\) is the unique element of the Toda bracket ",
  "\\(\\langle\\nu_5,8\\iota_8,\\nu_8\\rangle\\), and is the unique nonzero element ",
  "in \\(\\pi_{12}S^5\\).  See Toda's Lemma 5.13.  "
 )
):

TodaBracketRepresentation[sigmathird] := 
 TodaBracket[{nu[5],8 * iota[8],nu[8]},0]:

Indeterminacy[sigmathird] := {}:

DeclareElement(
 sigmasecond,"\\\sigma''",13,6,
 cat(
  "\\(\\sigma'':S^{13}\\rightarrow S^6\\) is characterised by the properties ",
  "\\(H(\\sigma'')=\\eta_{11}^2\\) and \\(\\E^3\\sigma''=4\\sigma_9\\). ",
  "It has order \\(4\\) and generates \\(\\pi_{13}S^6\\).  See Toda's ",
  "Lemma 5.14 (corrected by replacing \\(\\sigma''\\) by \\(sigma'\\) on ",
  "the second line), and note that ",
  "\\(\\E^3:\\pi_{13}^6\\rightarrow\\pi_{16}^9\\) is injective."
 )
):

Indeterminacy[sigmasecond] := {}:

DeclareElement(
 sigmaprime,"\\\sigma'",14,7,
 cat(
  "\\(\\sigma':S^{14}\\rightarrow S^7\\) is characterised by the properties ",
  "\\(H(\\sigma')=\\eta_{13}\\) and \\(\\E^2\\sigma'=2\\sigma_9\\). ",
  "It has order \\(8\\) and generates \\(\\pi_{14}S^7\\).  See Toda's ",
  "Lemma 5.14 (corrected by replacing \\(\\sigma''\\) by \\(sigma'\\) on ",
  "the second line), and note that ",
  "\\(\\E^2:\\pi_{14}^7\\rightarrow\\pi_{16}^9\\) is injective."
 )
):

Indeterminacy[sigmaprime] := {}:

DeclareElement(
 epsilonprime,"\\epsilon'",13,3,
 cat(
  "\\(\\epsilon':S^{13}\\rightarrow S^3\\) is the unique element of the Toda ",
  "bracket \\(\\langle\\nu',2\\nu_6,\\nu_9\\rangle_3\\).  ",
  "See Toda, Section VI(iv)."
 )
):

TodaBracketRepresentation[epsilonprime] := 
 TodaBracket[{nuprime,nuprime,nu[6]},3]:

Indeterminacy[epsilonprime] := {}:

DeclareElement(
 muprime,"\\mu'",14,3,
 cat(
  "The element \\(\\mu':S^{14}\\rightarrow S^3\\) lies in the Toda bracket ",
  "\\(\\langle\\eta_3,2\\iota_4,\\mu_4\\rangle_1\\) and satisfies ",
  "\\(H(\\mu')=\\mu_5\\) and \\(2\\mu'=\\eta_3\\circ\\eta_4\\circ\\mu_5\\); ",
  "this is explained at the beginning of Toda's ",
  "Section VII(ii).  Toda does not state the indeterminacy and I have not ",
  "worked it out."
 )
):

TodaBracketRepresentation[muprime] :=
 TodaBracket[{eta[3],2 * iota[3],mu[3]},1]:

DeclareElement(
 thetaprime,"\\theta'",23,11,
 cat(
  "\\(\\theta':S^{23}\\rightarrow S^{11}\\) is the unique element of the ",
  "Toda bracket \\(\\langle\\sigma_{11},2\\nu_{18},\\eta_{21}\\rangle_1\\) ",
  "and the unique nonzero element of \\(\\pi_{23}^{11}\\).  See ",
  "Toda's Lemma 7.5."
 )
):

TodaBracketRepresentation[thetaprime] := 
 TodaBracket[{sigma[11],2 * nu[17],eta[20]},1]:
Indeterminacy[thetaprime] := {}:

DeclareElement(
 theta,"\\theta",24,12,
 cat(
  "\\(\\theta:S^{24}\\rightarrow S^{12}\\) lies in the Toda bracket ",
  "\\(\\langle\\sigma_{12},\\nu_{19},\\eta_{22}\\rangle_1\\). ",
  "It is not clear whether the indeterminacy is zero."
 )
):

TodaBracketRepresentation[theta] := 
 TodaBracket[{sigma[12],nu[18],eta[21]},1]:

DeclareElement(
 rhofourth,"\\rho''''",20,5,
 cat(
  "\\(\\rho^{(4)}:S^{20}\\rightarrow S^5\\) is defined in Toda's ",
  "Section X(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma^{(3)},2\\iota_{12},8\\sigma_{12}\\rangle_1\\). ",
  "It is proved in the notes by Strickland that the indeterminacy is zero. "
 )
):

TodaBracketRepresentation[rhofourth] := 
 TodaBracket[{sigmathird,2 * iota[11],8 * sigma[11]},1]:
Indeterminacy[rhofourth] := {}:

DeclareElement(
 rhothird,"\\rho'''",21,6,
 cat(
  "\\(\\rho^{(3)}:S^{21}\\rightarrow S^6\\) is defined in Toda's ",
  "Section X(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma'',4\\iota_{13},4\\sigma_{13}\\rangle_1\\)."
 )
):

TodaBracketRepresentation[rhothird] := 
 TodaBracket[{sigmasecond,4 * iota[12],4 * sigma[12]},1]:

DeclareElement(
 rhosecond,"\\rho''",22,7,
 cat(
  "\\(\\rho'':S^{22}\\rightarrow S^7\\) is defined in Toda's ",
  "Section X(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma',8\\iota_{14},2\\sigma_{14}\\rangle_1\\). ",
  "We will take it to be the unique element for which ",
  "\\(H(\\rho'')=\\mu_{13}\\).  This is validated in the ",
  "notes by Strickland, prop-rho-second."
 )
):

TodaBracketRepresentation[rhosecond] := 
 TodaBracket[{sigmaprime,8 * iota[13],2 * sigma[13]},1]:

DeclareElement(
 rhoprime,"\\rho'",24,9,
 cat(
  "\\(\\rho':S^{24}\\rightarrow S^9\\) is defined in Toda's ",
  "Section X(iii) to be an element of the Toda bracket ",
  "\\(\\langle\\sigma_9,16\\iota_{16},\\sigma_{16}\\rangle_1\\)."
 )
):

TodaBracketRepresentation[rhoprime] := 
 TodaBracket[{sigma[9],16 * iota[15],sigma[15]},1]:

DeclareElement(
 zetaprime,"\\zeta'",22,6,
 cat(
  "\\(\\zeta':S^{22}\\rightarrow S^6\\) is the unique element such that ",
  "\\(H(\\zeta')=\\zeta_{11} mod 2\\zeta_{11}\\) and ",
  "\\(\\E\\zeta'=\\sigma'\\circ\\eta_{14}\\circ\\epsilon_{15}\\). ",
  "This is validated in the notes by Strickland, prop-zetaprime, which ",
  "refines Toda's Lemma 12.1."
 )
):

Indeterminacy[zetaprime] := {}:

DeclareElement(
 epsilonbarprime,"\\overline{\\epsilon}'",20,3,
 cat(
  "\\(\\epsilonbar':S^{20}\\rightarrow S^3\\) is defined in Toda's ",
  "Lemma 12.3 by the properties ",
  "\\(2\\epsilonbar'=\\eta_{3}\\circ\\eta_{4}\\circ\\epsilonbar_5\\) ",
  "and \\(\\E\\epsilonbar'=(\\E\\nu')\\circ\\kappa_{7}\\). ",
  "The map \\(\\E\\) here is injective by Toda's Theorem 12.7, ",
  "so this characterises \\(\\epsilonbar'\\) uniquely. "
 )
):

DeclareElement(
 mubarprime,"\\overline{\\mu}'",22,3,
 cat(
  "\\(\\mubar':S^{22}\\rightarrow S^3\\) is an element of the Toda ",
  "bracket \\(\\langle\\mu',4\\iota_{14},4\\sigma_{14}\\rangle_1\\). ",
  "See the preamble to Toda's Lemma 12.4. "
 )
):

TodaBracketRepresentation[mubarprime] := 
 TodaBracket[{muprime,4 * iota[13],4 * sigma[13]},1]:

DeclareElement(
 etastarprime,"{\\eta^*}'",31,15,
 cat(
  "\\({\\eta^*}':S^{31}\\rightarrow S^{15}\\) is an element of the ",
  "Toda bracket ",
  "\\(\\langle\\sigma_{15},4\\sigma_{22},\\eta_{29}\\rangle_1\\). ",
  "(There seems to be a filtration shift so this is not seen in Ext.) ",
  "See Toda's Section XII(iii). "
 )
):

TodaBracketRepresentation[etastarprime] := 
 TodaBracket[{sigma[15],4 * sigma[21],eta[28]},1]:

DeclareElement(
 lambdasecond,"\\lambda''",28,10,
 cat(
  "\\(\\lambda'':S^{28}\\rightarrow S^{10}\\) is defined in Toda's ",
  "Lemma 12.19 by the properties ",
  "\\(\\E\\lambda''=2\\lambda'\\) and ",
  "\\(H(\\lambda'')=\\eta_{19}\\circ\\epsilon_{20} mod ",
  "(\\eta_{19}\\circ\\epsilon_{20} + \\nu^3_{19}) \\).  ",
  "I have not checked the indeterminacy. "
 )
):

DeclareElement(
 xisecond,"\\xi''",28,10,
 cat(
  "\\(\\xi'':S^{28}\\rightarrow S^{10}\\) is defined in Toda's ",
  "Lemma 12.19 by the properties ",
  "\\(\\E\\xi''=2\\xi'\\) and ",
  "\\(H(\\xi'')=\\nu_{19}\\circ\\nu_{22}\\circ\\nu_{25}+\\eta_{13}\\circ\\epsilon_{20}\\). ",
  "I have not checked the indeterminacy. "
 )
):

DeclareElement(
 lambdaprime,"\\lambda'",29,11,
 cat(
  "\\(\\lambda':S^{29}\\rightarrow S^{11}\\) is defined in Toda's ",
  "Lemma 12.19 by the properties ",
  "\\(\\E^2\\lambda'=2\\lambda\\) and ",
  "\\(H(\\lambda')=\\epsilon_{21} mod (\\nubar_{21}+\\epsilon_{21})\\). ",
  "I have not checked the indeterminacy. "
 )
):

DeclareElement(
 xiprime,"\\xi'",29,11,
 cat(
  "\\(\\xi':S^{29}\\rightarrow S^{11}\\) is defined in Toda's ",
  "Lemma 12.19 by the properties ",
  "\\(\\E\\xi'=2\\xi_{12}\\pm w_{12}\\circ\\sigma_{23}\\) and ",
  "\\(H(\\xi')=\\nubar_{21}+\\epsilon_{21}\\). ",
  "I have not checked the indeterminacy. "
 )
):

DeclareElement(
 lambda,"\\lambda",31,13,
 cat(
  "\\(\\lambda:S^{31}\\rightarrow S^{13}\\) is defined in Toda's ",
  "Lemma 12.18 by the properties ",
  "\\(\\E^3\\lambda=2\\nu^*_{16}\\pm w_{16}\\circ\\nu_{31}\\) and ",
  "\\(H(\\lambda)=\\nu_{25}\\circ\\nu_{28}\\). ",
  "I have not checked the indeterminacy. "
 )
):

DeclareElement(
 omegaprime,"\\omega'",31,12,
 cat(
  "\\(\\omega':S^{31}\\rightarrow S^{12}\\) is defined in Toda's ",
  "Lemma 12.21 by the properties ",
  "\\(\\E^2\\omega'=2\\omega_{14}\\circ\\nu_{30}\\) and ",
  "\\(H(\\omega')=\\epsilon_{23} mod (\\nubar_{23}+\\epsilon_{23})\\). ",
  "I have not checked the indeterminacy. "
 )
):

######################################################################

# Orders of elements                                                  

AddOrderRule(
 w[n_],2,type(n_,odd),"Anticommutativity of the Whitehead product"
):

# 1-stem 
SetStableOrder(eta,2,3,"Toda, Proposition 5.1"):

# 2-stem 
AddOrderRule(
 o(eta[n_], eta[m_]), 
 2, 
 m_ = n_ + 1, 
 "\\(2\\eta_n\\circ\\eta_{n+1}=0\\) for \\(n\\geq 2\\)",
 "Toda, Proposition 5.3"
):

# 3-stem 
SetOrder(o(eta[2],eta[3],eta[4]),2,"Toda, Proposition 5.6"):
SetOrder(nuprime,4,"Toda, Proposition 5.6"):
SetOrder(E(nuprime),4,"Toda, Proposition 5.6"):
SetStableOrder(nu,8,5,"Toda, Proposition 5.6"):

# 4-stem 
SetOrder(o(eta[2],nuprime),4,"Toda, Proposition 5.8"):
SetOrder(o(nuprime,eta[6]),2,"Toda, Proposition 5.8"):
SetOrder(o(E(nuprime),eta[7]),2,"Toda, Proposition 5.8"):
AddOrderRule(
  o(nu[n_],eta[m_]),
  2,
  m_ = n_+3,
  "\\(2\\nu_n\\circ\\eta_{n+3}=0\\) for \\(n\\geq 2\\)",
  "Toda, Proposition 5.8"
):

# 5-stem 
SetOrder(o(eta[2],nuprime,eta[6]),2,"Toda, Proposition 5.9"):
SetOrder(o(nuprime,eta[6],eta[7]),2,"Toda, Proposition 5.9"):
SetOrder(o(E(nuprime),eta[7],eta[8]),2,"Toda, Proposition 5.9"):
SetOrder(o(nu[4],eta[7],eta[8]),2,"Toda, Proposition 5.9"):
SetOrder(o(nu[5],eta[8],eta[9]),2,"Toda, Proposition 5.9"):

# 6-stem 
SetOrder(o(eta[2],nuprime,eta[6],eta[7]),2,"Toda, Proposition 5.11"):
SetOrder(o(nu[4],nu[7]),8,"Toda, Proposition 5.11"):
AddOrderRule(
  o(nu[n_],nu[m_]),
  2,
  (n_ >= 5) and (m_ = n+3),
  "\\(2\\nu_n\\circ\\nu_{n+3}=0\\) for \\(n\\geq 5\\)",
  "Toda, Proposition 5.11"
):

# 7-stem 
SetOrder(sigmathird,2,"Toda, Proposition 5.15"):
SetOrder(sigmasecond,  4,"Toda, Proposition 5.15"):
SetOrder(sigmaprime,8,"Toda, Proposition 5.15"):
SetOrder(E(sigmaprime),8,"Toda, Proposition 5.15"):
SetStableOrder(sigma,16,9,"Toda, Proposition 5.15"):

# 8-stem 
SetStableOrder(epsilon,2,3,"Toda, Theorem 7.1"):
SetOrder(nubar[6],8,"Toda, Theorem 7.1"):
SetStableOrder(nubar,2,7,"Toda, Theorem 7.1"):
SetOrder(o(sigmaprime,eta[14]),2,"Toda, Theorem 7.1"):
SetOrder(o(E(sigmaprime),eta[15]),2,"Toda, Theorem 7.1"):
SetOrder(o(sigma[8],eta[15]),2,"Toda, Theorem 7.1"):
SetOrder(o(sigma[9],eta[16]),2,"Toda, Theorem 7.1"):

# 9-stem 
AddOrderRule(
  o(eta[n_],epsilon[m_]), 2, m_ = n_+1,
  "\\(2\\eta_n\\circ\\epsilon_{n+1}=0\\) for \\(n\\geq 2\\)",
  "Toda, Theorem 7.2"
):
SetStableOrder(mu,2,3,"Toda, Theorem 7.2"):

AddOrderRule(
  o(nu[n_],nu[m_],nu[p_]), 2,(m_ = n_+3) and (p_ = m_+3),
  "\\(2(\\nu_n\\circ\\nu_{n+3}\\circ\\nu_{n+6})=0\\) for \\(n\\geq 4\\)",
  "Toda, Theorem 7.2"
):

SetOrder(o(sigmaprime,eta[14],eta[15]),2,"Toda, Theorem 7.2"):
SetOrder(o(E(sigmaprime),eta[15],eta[16]),2,"Toda, Theorem 7.2"):
SetOrder(o(sigma[8],eta[15],eta[16]),2,"Toda, Theorem 7.2"):
SetOrder(o(sigma[9],eta[16],eta[17]),2,"Toda, Theorem 7.2"):

# 10-stem 

SetOrder(o(eta[2],eta[3],epsilon[4]),2,"Toda, Theorem 7.3"):

AddOrderRule(o(eta[n_],mu[m_]),2,m_ = n_+1,
 "\\(2\\eta_n\\circ\\mu_{n+1}=0\\) for \\(n\\geq 2\\)",
 "Toda, Theorem 7.3"
):

SetOrder(epsilonprime,4,"Toda, Theorem 7.3"):
SetOrder(E(epsilonprime),4,"Toda, Theorem 7.3"):
SetOrder(o(nu[ 4],sigmaprime),8,"Toda, Theorem 7.3"):
SetOrder(o(nu[ 5],sigma[ 8]),8,"Toda, Theorem 7.3"):
SetOrder(o(nu[ 6],sigma[ 9]),8,"Toda, Theorem 7.3"):
SetOrder(o(nu[ 7],sigma[10]),8,"Toda, Theorem 7.3"):
SetOrder(o(nu[ 8],sigma[11]),8,"Toda, Theorem 7.3"):
SetOrder(o(sigma[ 8],nu[15]),8,"Toda, Theorem 7.3"):
SetOrder(o(sigma[ 9],nu[16]),8,"Toda, Theorem 7.3"):
SetOrder(o(sigma[10],nu[17]),4,"Toda, Theorem 7.3"):
SetOrder(o(sigma[11],nu[18]),2,"Toda, Theorem 7.3"):

# 11-stem 
SetOrder(o(eta[2],epsilonprime),4,"Toda, Theorem 7.4"):
SetOrder(o(eta[2],eta[3],mu[4]),2,"Toda, Theorem 7.4"):
SetOrder(muprime,4,"Toda, Theorem 7.4"):
SetOrder(E(muprime),4,"Toda, Theorem 7.4"):
SetOrder(o(epsilon[3],nu[11]),2,"Toda, Theorem 7.4"):
SetOrder(o(epsilon[4],nu[12]),2,"Toda, Theorem 7.4"):
SetOrder(o(nuprime,epsilon[6]),2,"Toda, Theorem 7.4"):
SetOrder(o(E(nuprime),epsilon[7]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[4],sigmaprime,eta[14]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[ 4],nubar[7]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[ 5],nubar[8]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[ 4],epsilon[7]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[ 5],epsilon[8]),2,"Toda, Theorem 7.4"):
SetStableOrder(zeta,8,5,"Toda, Theorem 7.4"):
SetOrder(o(nubar[ 6],nu[14]),4,"Toda, Theorem 7.4"):
SetOrder(o(nubar[ 7],nu[15]),2,"Toda, Theorem 7.4"):
SetOrder(o(nubar[ 8],nu[16]),2,"Toda, Theorem 7.4"):
SetOrder(o(nubar[ 9],nu[17]),2,"Toda, Theorem 7.4"):
SetOrder(o(nu[5],sigma[8],eta[15]),2,
 "\\(\\alpha\\circ\\eta_n\\) is always killed by 2 when \\(n>2\\)."
):

# 12-stem 
SetOrder(o(eta[2],muprime),4,"Toda, Theorem 7.6"):
SetOrder(o(eta[2],epsilon[3],nu[11]),2,"Toda, Theorem 7.6 and Equations 7.12"):
SetOrder(o(eta[2],nuprime,epsilon[6]),2,"Toda, Theorem 7.6"):
SetOrder(o(nuprime,mu[6]),2,"Toda, Theorem 7.6"):
SetOrder(o(nuprime,eta[6],epsilon[7]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[4],sigmaprime,eta[14],eta[15]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[4],nu[7],nu[10],nu[13]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[4],mu[7]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[4],eta[7],epsilon[8]),2,"Toda, Theorem 7.6"):
SetOrder(o(E(nuprime),mu[7]),2,"Toda, Theorem 7.6"):
SetOrder(o(E(nuprime),eta[7],epsilon[8]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[5],nu[8],nu[11],nu[14]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[5],mu[8]),2,"Toda, Theorem 7.6"):
SetOrder(o(nu[5],eta[8],epsilon[9]),2,"Toda, Theorem 7.6"):
SetOrder(o(w[6],sigma[11]),16,"Toda, Theorem 7.6"):
SetOrder(o(w[10],nu[19]),4,"Toda, Theorem 7.6"):
SetOrder(thetaprime,2,"Toda, Theorem 7.6"):
SetOrder(E(thetaprime),2,"Toda, Theorem 7.6"):
SetOrder(theta,2,"Toda, Theorem 7.6"):
SetOrder(E(theta),2,"Toda, Theorem 7.6"):

# 13-stem 

SetOrder(o(eta[2],nuprime,mu[6]),2,"Toda, Theorem 7.7"):
SetOrder(o(eta[2],nuprime,eta[6],epsilon[7]),2,"Toda, Theorem 7.7"):
SetOrder(o(nuprime,eta[6],mu[7]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[4],nu[7],sigma[10]),8,
 "Toda, Theorem 7.7.  Note that Toda refers to \\(\\nu_4^2\\circ\\sigma_8=\\nu_4\\circ\\nu_7\\circ\\sigma_8\\) instead of \\(\\nu_4^2\\circ\\sigma_{10}\\).  This is not dimensionally consistent, and is a typo. "):
SetOrder(o(nu[4],eta[7],mu[8]),2,"Toda, Theorem 7.7"):
SetOrder(o(E(nuprime),eta[7],mu[8]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[5],sigma[ 8],nu[15]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[6],sigma[ 9],nu[16]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[7],sigma[10],nu[17]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[8],sigma[11],nu[18]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[5],eta[8],mu[9]),2,"Toda, Theorem 7.7"):
SetOrder(o(sigma[ 8],nu[15],nu[18]),2,"Toda, Theorem 7.7"):
SetOrder(o(sigma[ 9],nu[16],nu[19]),2,"Toda, Theorem 7.7"):
SetOrder(o(sigma[10],nu[17],nu[20]),2,"Toda, Theorem 7.7"):
SetOrder(o(sigma[11],nu[18],nu[21]),2,"Toda, Theorem 7.7"):
SetOrder(o(nu[8],sigma[11],nu[18]),2,"Toda, Theorem 7.7"):
SetOrder(o(thetaprime,eta[23]),2,"Toda, Theorem 7.7"):
SetOrder(o(theta,eta[24]),2,"Toda, Theorem 7.7"):
SetOrder(o(E(thetaprime),eta[24]),2,"Toda, Theorem 7.7"):
SetOrder(o(E(theta),eta[25]),2,"Toda, Theorem 7.7"):

# 14-stem 

SetOrder(o(eta[2],nuprime,eta[6],mu[7]),2,"Toda, Theorem 10.3"):
SetOrder(o(epsilon[3],nu[11],nu[14]),2,"Toda, Theorem 10.3"):
SetOrder(o(epsilon[4],nu[12],nu[15]),2,"Toda, Theorem 10.3"):
SetOrder(o(nu[4],zeta[7]),8,"Toda, Theorem 10.3"):
SetOrder(o(nu[4],nubar[7],nu[15]),2,"Toda, Theorem 10.3"):
SetOrder(o(nu[5],zeta[8]),2,"Toda, Theorem 10.3"):
SetOrder(o(nu[5],nubar[8],nu[16]),2,"Toda, Theorem 10.3"):
SetOrder(o(sigmasecond,sigma[13]),4,"Toda, Theorem 10.3"):
SetOrder(o(nubar[6],nu[14],nu[17]),2,"Toda, Theorem 10.3"):
SetOrder(o(sigmaprime,sigma[14]),8,"Toda, Theorem 10.3"):
SetOrder(o(E(sigmaprime),sigma[15]),8,"Toda, Theorem 10.3"):

SetOrder(kappa[7],4,"Toda, Theorem 10.3"):
SetOrder(kappa[8],4,"Toda, Theorem 10.3"):
SetOrder(kappa[9],4,"Toda, Theorem 10.3"):
SetStableOrder(kappa,2,10,"Toda, Theorem 10.3"):

SetOrder(o(sigma[ 8],sigma[15]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[ 9],sigma[16]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[10],sigma[17]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[11],sigma[18]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[12],sigma[19]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[13],sigma[20]),16,"Toda, Theorem 10.3"):
SetOrder(o(sigma[14],sigma[21]),8,"Toda, Theorem 10.3"):
SetOrder(o(sigma[15],sigma[22]),4,"Toda, Theorem 10.3"):
AddOrderRule(
 o(sigma[n_],sigma[m_]),
 2,
 m_ = n_+7 and n >= 16,
 "\\(2{\\sigma_n}\\circ{\\sigma_{n+7}}=0\\) for \\(n\\geq 16\\)",
 "Toda, Theorem 10.3"
):

SetOrder(o(w[12],nu[23]),4,"Toda, Theorem 10.3"):

# 15-stem 

SetStableOrder(epsilonbar,2,3,"Toda, Theorem 10.5"):
SetStableOrder(rho,32,13,"Toda, Theorem 10.10"):

SetOrder(o(eta[2],epsilon[3],nu[11],nu[14]),2,"Toda, Theorem 10.5"):
SetOrder(rhofourth,2,"Toda, Theorem 10.5"):
SetOrder(rhothird,4,"Toda, Theorem 10.5"):
SetOrder(rhosecond,8,"Toda, Theorem 10.5"):
SetOrder(E(rhosecond),8,"Toda, Theorem 10.5"):
SetOrder(rhoprime,16,"Toda, Theorem 10.5"):
SetOrder(E(rhoprime),16,"Toda, Theorem 10.5"):
SetOrder(E(E[rhoprime]),16,"Toda, Theorem 10.5"):
SetOrder(E(E[E[rhoprime]]),16,"Toda, Theorem 10.5"):

SetOrder(o(sigmaprime,nubar[14]),2,"Toda, Theorem 10.5"):
SetOrder(o(E(sigmaprime),nubar[15]),2,"Toda, Theorem 10.5"):
SetOrder(o(sigma[8],nubar[15]),2,"Toda, Theorem 10.5"):
SetOrder(o(sigma[9],nubar[16]),2,"Toda, Theorem 10.5"):
SetOrder(o(sigma[10],nubar[17]),2,"Toda, Theorem 10.5"):

SetOrder(o(sigmaprime,epsilon[14]),2,"Toda, Theorem 10.5"):
SetOrder(o(E(sigmaprime),epsilon[15]),2,"Toda, Theorem 10.5"):
SetOrder(o(sigma[8],epsilon[15]),2,"Toda, Theorem 10.5"):
SetOrder(o(sigma[9],epsilon[16]),2,"Toda, Theorem 10.5"):

# 16-stem 

SetStableOrder(omega,2,15,"Toda, Theorem 12.16"):
SetStableOrder(etastar,2,16,"Toda, Theorem 12.16"):

AddOrderRule(
 o(mu[n_], sigma[m_]), 
 2, 
 m_ = n_ + 9 and n_ >= 3, 
 "\\(2\\mu_n\\circ\\sigma_{n+9}=0\\) for \\(n\\geq 3\\)",
 cat(
  "Toda, Theorem 12.6 (with the observation that stably we ",
  "have \\(\\mu\\sigma=\\sigma\\mu\\))."
 )
):

AddOrderRule(
 o(sigma[n_], mu[m_]), 
 2, 
 m_ = n_ + 7 and n_ >= 8, 
 "\\(2\\sigma_n\\circ\\mu_{n+7}=0\\) for \\(n\\geq 8\\)",
 "Toda, Theorem 12.6"
):


AddOrderRule(
 o(eta[n_], epsilonbar[m_]), 
 2, 
 m_ = n_ + 1 and n_ >= 2 and n_ <= 8, 
 "\\(2\\eta_n\\circ\\epsilonbar_{n+1}=0\\) for \\(2\\leq n\\leq 8\\)",
 "Toda, Theorem 12.6"
):

SetOrder(zetaprime,8,"Toda, Theorem 12.6"):
SetOrder(E(zetaprime),2,"Toda, Theorem 12.6"):
SetOrder(E(E[zetaprime]),2,"Toda, Theorem 12.6"):
SetOrder(etastarprime,2,"Toda, Theorem 12.16"):
SetOrder(E(etastarprime),2,"Toda, Theorem 12.16"):
SetOrder(o(sigmaprime,mu[14]),2,"Toda, Theorem 12.6"):
SetOrder(o(E(sigmaprime),mu[15]),2,"Toda, Theorem 12.6"):
SetOrder(o(nu[4],nu[7],sigma[10],nu[17]),2,"Toda, Theorem 12.6"):
SetOrder(o(sigma[8],eta[15],epsilon[16]),2,"Toda, Theorem 12.6"):
SetOrder(o(sigma[9],eta[16],epsilon[17]),2,"Toda, Theorem 12.6"):
SetOrder(o(sigma[8],nu[15],nu[18],nu[21]),2,"Toda, Theorem 12.6"):
SetOrder(o(sigma[9],nu[16],nu[19],nu[22]),2,"Toda, Theorem 12.6"):
SetOrder(o(w[10],sigma[19]),16,"Toda, Theorem 12.16"):
SetOrder(omega[14],8,"Toda, Theorem 12.16"):

# 17-stem 


SetStableOrder(epsilonstar,2,12,"Toda, Theorem 12.17"):
SetStableOrder(mubar,2,3,"Toda, Theorem 12.7"):

SetOrder(epsilonbarprime,4,"Toda, Theorem 12.7"):
SetOrder(E(epsilonbarprime),4,"Toda, Theorem 12.7"):
SetOrder(WhiteheadP[E(theta)],2,"Toda, Theorem 12.8"):
SetOrder(o(etastarprime,eta[31]),2,"Toda, Theorem 12.17"):
SetOrder(o(E(etastarprime),eta[32]),2,"Toda, Theorem 12.17"):
SetOrder(o(sigmaprime,eta[14],mu[15]),2,"Toda, Theorem 12.7"):
SetOrder(o(E(sigmaprime),eta[15],mu[16]),2,"Toda, Theorem 12.7"):
SetOrder(o(eta[2],eta[3],epsilonbar[4]),2,"Toda, Theorem 12.7"):
SetOrder(o(etastar[16],eta[32]),2,"Toda, Theorem 12.17"):
SetOrder(o(etastar[17],eta[33]),2,"Toda, Theorem 12.17"):
SetOrder(o(nu[4],sigmaprime,sigma[14]),8,"Toda, Theorem 12.7"):
SetOrder(w[18],infinity,"Toda, Theorem 12.17"):
SetOrder(o(nu[ 4],kappa[ 7]),4,"Toda, Theorem 12.7"):
SetOrder(o(nu[ 5],kappa[ 8]),4,"Toda, Theorem 12.7"):
SetOrder(o(nu[ 6],kappa[ 9]),4,"Toda, Theorem 12.7"):


AddOrderRule(
  o(eta[n_],mu[m_],sigma[p_]),2,(m_ = n_+1) and (p_ = m_+9),
  "\\(2\\eta_n\\circ\\mu_{n+1}\\circ\\sigma_{n+10}=0\\) for \\(n\\geq 2\\)",
  "Toda, Theorem 12.7"
):


AddOrderRule(
  o(nu[n_],kappa[m_]),2, (m_ = n_+3) and (n_ >= 8),
  "\\(2\\nu_n\\circ\\kappa_{n+3}=0\\) for \\(n\\geq 8\\)",
  "Toda, Theorem 12.7"
):

AddOrderRule(
  o(sigma[n_],eta[m_],mu[p_]),2, (m_ = n_+7) and (p_ = m_+1),
  "\\(2\\sigma_n\\circ\\eta_{n+7}\\circ\\mu_{n+8}=0\\) for \\(n\\geq 8\\).",
  "Toda, Theorem 12.7"
):

# 18-stem 

SetStableOrder(nustar,8,16,"Toda, Theorem 12.22"):
SetStableOrder(xi,8,13,"Toda, Theorem 12.22"):

SetOrder(xi[18]+nustar[18],4,"Toda, Theorem 12.22"):
SetOrder(xi[19]+nustar[19],2,"Toda, Theorem 12.22"):

SetOrder(lambdasecond,8,"Toda, Theorem 12.22"):
SetOrder(lambdaprime,8,"Toda, Theorem 12.22"):
SetOrder(E(lambdaprime),4,"Toda, Theorem 12.22"):
SetOrder(lambda,8,"Toda, Theorem 12.22"):
SetOrder(E(lambda),8,"Toda, Theorem 12.22"):
SetOrder(E(E[lambda]),8,"Toda, Theorem 12.22"):
SetOrder(E(E[E[lambda]]),8,"Toda, Theorem 12.22"):
SetOrder(xisecond,2,"Toda, Theorem 12.22"):
SetOrder(xiprime,4,"Toda, Theorem 12.22"):
SetOrder(E(xiprime),4,"Toda, Theorem 12.22"):
SetOrder(o(E(muprime),sigma[15]),4,"Toda, Theorem 12.8"):
SetOrder(o(E(nuprime),epsilonbar[7]),2,"Toda, Theorem 12.8"):
SetOrder(o(WhiteheadP[E(theta)],eta[23]),2,"Toda, Theorem 12.8"):
SetOrder(o(eta[2],epsilonbarprime),4,"Toda, Theorem 12.8"):
SetOrder(o(eta[2],eta[3],mu[4],sigma[13]),2,"Toda, Theorem 12.8"):
SetOrder(o(muprime,sigma[14]),4,"Toda, Theorem 12.8"):
SetOrder(o(nu[4],epsilonbar[7]),2,"Toda, Theorem 12.8"):
SetOrder(o(nu[4],rhosecond),8,"Toda, Theorem 12.8"):
SetOrder(o(nu[4],sigmaprime,epsilon[14]),2,"Toda, Theorem 12.8"):
SetOrder(o(nu[4],sigmaprime,nubar[14]),2,"Toda, Theorem 12.8"):
SetOrder(o(nu[5],epsilonbar[8]),2,"Toda, Theorem 12.8"):
SetOrder(o(nuprime,epsilonbar[6]),2,"Toda, Theorem 12.8"):

SetOrder(o(sigma[8],zeta[15]),8,"Toda, Theorem 12.8"):
SetOrder(o(sigma[9],zeta[16]),8,"Toda, Theorem 12.8"):
SetOrder(o(zeta[5],sigma[16]),8,"Toda, Theorem 12.8"):
SetOrder(o(zeta[6],sigma[17]),8,"Toda, Theorem 12.8"):
SetOrder(o(zeta[7],sigma[18]),8,"Toda, Theorem 12.8"):
SetOrder(o(zeta[8],sigma[19]),8,"Toda, Theorem 12.8"):

SetOrder(xi[12],32,"Toda, Theorem 12.22"):

### FIX THIS
# AddRelation[4 xi[18] -> 4 nustar[18],"Toda, Theorem 12.22"]
# AddRelation[
#  n_Integer xi[m_] :>
#   2 Quotient[n,2] nustar[m] + Mod[n,2] xi[m] /; 
#    (m >= 19) and (n < 0 || n > 1),
#  "\\(2(\\xi_n+\\nu^*_n)=0\\) for \\(n\\geq 19\\)",
#  "Toda, Theorem 12.22"
# ]

AddOrderRule(
  o(eta[n_],mubar[m_]),2,m_ = n_+1,
  "\\(2\\eta_n\\circ\\mubar_{n+1}=0\\) for \\(n\\geq 2\\)",
  "Toda, Theorem 12.8"
):
 

# 19-stem 

SetOrder(mubarprime,4,"Toda, Theorem 12.9"):
SetOrder(E(mubarprime),4,"Toda, Theorem 12.9"):

SetOrder(omegaprime,2,"Toda, Theorem 12.23"):
SetOrder(E(omegaprime),2,"Toda, Theorem 12.23"):

SetOrder(o(lambdaprime,eta[29]),2,"Toda, Theorem 12.23"):
SetOrder(o(E(lambdaprime),eta[30]),2,"Toda, Theorem 12.23"):

SetOrder(o(nuprime,mu[6],sigma[15]),2,"Toda, Theorem 12.9"):
SetOrder(o(E(nuprime),mu[7],sigma[16]),2,"Toda, Theorem 12.9"):
SetOrder(o(nu[4],mu[7],sigma[16]),2,"Toda, Theorem 12.9"):
SetOrder(o(nu[5],mu[8],sigma[17]),2,"Toda, Theorem 12.9"):

SetOrder(o(xiprime,eta[29]),2,"Toda, Theorem 12.23"):
SetOrder(o(E(xiprime),eta[30]),2,"Toda, Theorem 12.23"):
SetOrder(o(xi[12],eta[30]),2,"Toda, Theorem 12.23"):
SetOrder(o(xi[13],eta[31]),2,"Toda, Theorem 12.23"):

SetOrder(o(eta[2],eta[3],mubar[4]),2,"Toda, Theorem 12.9"):
SetOrder(o(eta[2],muprime,sigma[14]),4,"Toda, Theorem 12.9"):
SetOrder(o(eta[2],nuprime,epsilonbar[6]),2,"Toda, Theorem 12.9"):

SetOrder(o(nu[4],E(zetaprime)),2,"Toda, Theorem 12.9"):
SetOrder(o(nu[4],eta[7],epsilonbar[8]),2,"Toda, Theorem 12.9"):
SetOrder(o(nu[4],sigmaprime,mu[14]),2,"Toda, Theorem 12.9"):

SetOrder(o(omega[14],nu[30]),4,"Toda, Theorem 12.23"):
SetOrder(o(omega[15],nu[31]),2,"Toda, Theorem 12.23"):
SetOrder(o(omega[16],nu[32]),2,"Toda, Theorem 12.23"):
SetOrder(o(omega[17],nu[32]),2,"Toda, Theorem 12.23"):

SetOrder(sigmabar[6],32,"Toda, Theorem 12.9"):
SetStableOrder(sigmabar,2,7,"Toda, Theorem 12.9"):
SetStableOrder(zetabar,8,5,"Toda, Theorem 12.9"):

SetOrder(w[20],infinity,"Toda, Theorem 12.9"):

######################################################################
# Here we give some information about orders of elements x that are not
# chosen generators of the groups in which they live.  We hope to be   
# able to write x in terms of standard generators, at which point this 
# information will become redundant.                                   

SetOrder(o(nu[9],sigma[12]),4,"Toda, Equations 7.20"):
SetOrder(o(nu[10],sigma[13]),2,"Toda, Equations 7.20"):
SetOrder(o(sigma[11],zeta[18]),2,"Toda, Equations 12.23"):
SetOrder(o(sigma[10],zeta[17]),4,"Toda, Equations 12.23"):

######################################################################

AddRelation(
 epsilonstar[14],
 true,
 o(omega[14],eta[30]),
 "Toda, Lemma 12.15"
):

AddRelation(
 etastar[n],
 n >= 18,
 Coset(omega[n],{o(sigma[n],mu[n+7])}),
 "\\(\\eta^*_n={\\omega_n} mod {\\sigma_n}\\circ{\\mu_{n+7}}\\) for \\(n\\geq 18\\)",
 "Toda, Proposition 12.20(ii)"
):

AddRelation(
 xi[n],
 n >= 20,
 - nustar[n],
 "\\(\\xi_n=-\\nu^*_n\\) for \\(n\\geq 20\\)",
 "Toda, Corollary 12.25"
):

######################################################################
# Suspensions                                                          

AddRelation(
 E(E(nuprime)),
 true,
 2 * nu[5],
 "Toda, Lemma 5.4"
):

AddRelation(
 E(sigmathird),
 true,
 2 * sigmasecond,
 "Toda, Lemma 5.14"
):

AddRelation(
 E(sigmasecond),
 true,
 2 * sigmaprime,
 "Toda, Lemma 5.14"
):

AddRelation(
 E(E(sigmasecond)),
 true,
 2 * E(sigma[8]),
 "Toda, Lemma 5.14"
):


AddRelation(
 E(E(sigmaprime)),
 true,
 2 * sigma[9],
 "In the proof of Toda's Lemma 5.14 we have \\(\\E^2\\sigma'=2x\\E\\alpha^*\\).  The final statement in the proof shows that \\(\\sigma_9=\\E\\sigma_8=x\\E\\alpha^*\\), so \\(\\E^2\\sigma'=2\\sigma_9\\). "
):


AddRelation(
 E(E(epsilonprime)),
 true,
 2 * o(nu[5],sigma[8]),
 "Toda, Equations 7.10.  We have fudged a sign."
):

AddRelation(
 E(E(muprime)),
 true,
 2 * zeta[5],
 "Toda, Equations 7.14.  We have fudged a sign."
):

AddRelation(
 E(E(theta)),
 true,
 0,
 "Toda, Equations 7.30 says that \\(\\E\\theta\\) is in the image of P "
):

AddRelation(
 E(E(thetaprime)),
 true,
 0,
 "Toda, Equations 7.30 says that \\(\\E\\theta'\\) is in the image of P "
):

AddRelation(
 E(E(E(E(rhoprime)))),
 true,
 2 * rho(13),
 "Toda, Lemma 10.9"
):

AddRelation(
 E(E(lambdaprime)),
 true,
 2 * lambda,
 "Toda, Lemma 12.19"
):

AddRelation(
 E(E(mubarprime)),
 true,
 2 * zetabar[5],
 "Toda, Lemma 12.4"
):

AddRelation(
 E(E(omegaprime)),
 true,
 2 * o(omega[14],nu[30]),
 "Toda, Equations 12.27"
):

AddRelation(
 E(E(rhosecond)),
 true,
 2 * rhoprime,
 "Toda, Remark before Lemma 10.7"
):

AddRelation(
 E(lambdasecond),
 true,
 2 * lambdaprime,
 "Toda, Lemma 12.19"
):


AddRelation(
 E(rhofourth),
 true,
 2 * rhothird,
 "Toda, Equations 10.15"
):

AddRelation(E(rhothird),
 true,
 2 * rhosecond,
 "Toda, Equations 10.16"
):

AddRelation(
 E(xisecond),
 true,
 2 * xiprime,
 "Toda, Lemma 12.19"
):

AddRelation(
 E(E(E(zetaprime))),
 true,
 0,
 cat(
  "Toda, Lemma 12.1 (together with the fact that \\(2\\pi_{23}^7=0\\)) ",
  "gives \\(\\E\\zeta'=\\sigma'\\circ\\eta_{14}\\circ\\epsilon_{15}\\).  ",
  "We now suspend this twice and note that $\\E^{2}\\sigma'=2\\sigma_9\\) ",
  "and \\(2\\eta_{16}=0\\) to get \\(\\E^3\\zeta'=0\\). "
 )
):

AddRelation(
 E(E(epsilonbarprime)),
 true,
 2 * o(nu[5],kappa[8]),
 cat(
  "Suspend the relation ",
  "\\(\\E{\\epsilonbar'}=(\\E\\nu')\\circ\\kappa_7\\), ",
  "which is part of the definition of \\(\\epsilonbar'\\)."
 )
):

######################################################################

# Composition                                                          

AddRelation(
 o(eta[3],eta[4],eta[5]),
 true,
 2 * nuprime,
 "Toda, Equations 5.3"
):

AddRelation(
 o(eta[4],eta[5],eta[6]),
 true,
 2 * E(nuprime),
 "Toda, Equations 5.3"
):

AddRelation(
 o(eta[k_],eta[l_],eta[m_]),
 l_ = k_+1 and m_ = l_+1 and k_>=5,
 4 * nu[k_],
 "\\({\\eta_k}\\circ{\\eta_{k+1}}\\circ{\\eta_{k+2}}=4\\nu_k\\) for \\(k\\geq 5\\)",
 "Toda, Equations 5.5"
):

AddRelation(
 o(eta[3],E(nuprime)),
 true,
 0,
 "Toda, Lemma 5.7"
):

AddRelation(
 o(eta[n_],nu[m_]),
 m_ = n_+1 and n_ >= 5,
 0,
 "\\({\\eta_n}\\circ{\\nu_{n+1}}=0\\) for \\(n\\geq 5\\)",
 "Toda, Equations 5.9" 
):

AddRelation(
 o(nu[n_],eta[m_]),
 m_ = n_+3 and n_ >= 6,
 0,
 "\\({\\nu_n}\\circ{\\eta_{n+3}}=0\\) for \\(n\\geq 6\\)",
 "Toda, Equations 5.9" 
):

AddRelation(
 o(nuprime,nu[6]),
 true,
 0,
 "This is in \\(\\pi_9S^3=0\\) --- see Toda, Section V(vi)"
):

AddRelation(
 o(E(nuprime),nu[7]),
 true,
 0,
 "This is the suspension of the relation \\(\\nu'\\circ\\nu_6=0\\), which takes place in \\(\\pi_9S^3=0\\) --- see Toda, Section V(vi). "
):

AddRelation(
 o(epsilon[n_],nu[m_]),
 m_ = n_+8 and n_>=5,
 0 ,
 "\\({\\epsilon_n}\\circ{\\nu_{n+8}}=0\\) for \\(n\\geq 5\\)",
 "Toda's Equations 7.13 say that \\(\\epsilon_4\\circ\\nu_{12}=P(\\epsilon_9)\\), and we can suspend this to see that \\(\\epsilon_5\\circ\\nu_{13}=0\\). "
):

AddRelation(
 o(sigmathird,eta[12]),
 true,
 0,
 "Toda, Equations 7.4"
):

AddRelation(
 o(eta[3],E(epsilonprime)),
 true,
 0,
 "Notes by Strickland"
):

AddRelation(
 o(eta[5],sigmasecond),
 true,
 0,
 "Toda, Equations 7.4"
):
 
AddRelation(
 o(eta[4],sigmathird),
 true,
 0,
 "Toda, Equations 7.4"
):
 
AddRelation(
 o(eta[3],nu[4]),
 true,
 o(nuprime,eta[6]),
 "Toda, Equations 5.9"
):

AddRelation(
 o(eta[3],eta[4],epsilon[5]),
 true,
 2 * epsilonprime,
 "Toda, Lemma 6.6"
):

AddRelation(
 o(eta[3],eta[4],mu[5]),
 true,
 2 * muprime,
 "Toda, beginning of Section VII(ii)"
):

AddRelation(
 o(eta[4],eta[5],mu[6]),
 true,
 2 * E(muprime),
 "Suspend the relation \\(\\eta_3\\circ\\eta_4\\circ\\mu_5=2\\mu'\\) given by Toda at the beginning of Section VII(ii)."
):

AddRelation(
 o(eta[5],eta[6],mu[7]),
 true,
 4 * zeta[5],
 "Toda, proof of Equations 7.13"
):

AddRelation(
 o(eta[4],nu[5]),
 true,
 o(E(nuprime),eta[7]),
 "Toda, Equations 5.9, suspended once"
):

AddRelation(
 o(nu[5],E(sigmaprime)),
 true,
 2 * o(nu[5],sigma[8]),
 "Toda, Equations 7.16"
):

AddRelation(
 o(nubar[n_],eta[m_]),
 m_ = n_+8 and n_ > 5,
 o(nu[n_],nu[n_+3],nu[n_+6]) ,
 "\\({\\nubar_n}\\circ{\\eta_{n+8}}={\\nu_n}\\circ{\\nu_{n+3}}\\circ{\\nu_{n+6}}\\) for \\(n\\geq 6\\)",
 "Toda, Lemma 6.3"
):

AddRelation(
 o(eta[n_],nubar[m_]) ,
 m_ = n_+1 and n_ > 5,
 o(nu[n_],nu[n_+3],nu[n_+6]) ,
 "\\({\\eta_n}\\circ{\\nubar_{n+1}}={\\nu_n}\\circ{\\nu_{n+3}}\\circ{\\nu_{n+6}}\\) for \\(n\\geq 6\\)",
 "Toda, Lemma 6.3"
):

AddRelation(
 o(eta[n_],sigma[m_]) ,
 m_ = n_+1 and n_ >= 9,
 nubar[n_] + epsilon[n_] ,
 "\\({\\eta_n}\\circ{\\sigma_{n+1}}=\\nubar_n+\\epsilon_n\\) for \\(n\\geq 9\\)",
 "Toda, Lemma 6.4"
):

AddRelation(
 o(sigma[n_],eta[m_]),
 m_ = n_+7 and n_>9,
 nubar[n_] + epsilon[n_],
 "\\({\\sigma_n}\\circ{\\eta_{n+7}}=\\nubar_n+\\epsilon_n\\) for \\(n\\geq 9\\)",
 "Toda, Lemma 6.4"
):


AddRelation(
 o(eta[7],sigma[8]),
 true,
 o(sigmaprime,eta[14]) + nubar[7] + epsilon[7],
 "Toda, Equations 7.4"
):

AddRelation(
 o(eta[8],sigma[9]),
 true,
 o(E(sigmaprime),eta[15]) + nubar[8] + epsilon[8],
 "Suspension of Toda's Equations 7.4"
):

AddRelation(
 o(eta[6],sigmaprime),
 true,
 4 * nubar[6],
 "Toda, Equations 7.4"
):

AddRelation(
 o(sigmasecond,eta[13]),
 true,
 4 * nubar[6],
 "Toda, Equations 7.4"
):

AddRelation(
 o(epsilon[n_],eta[m_]),
 m_ = n_+8,
 o(eta[n_],epsilon[n_+1]),
 "Toda, Equations 7.5"
):

AddRelation(
 o(eta[n_],eta[m_],epsilon[p_]),
 m_ = n_+1 and p_ = n_+2 and n_ > 4,
 4 * o(nu[n_],sigma[n_+3]),
 "Toda, Equations 7.10"
):

AddRelation(
 o(nuprime,nubar[6]),
 true,
 o(epsilon[3],nu[11]),
 "Toda, Equations 7.12"
):

AddRelation(
 o(nuprime,w[6]),
 true,
 0,
 "As \\(\\E w_6=0\\) we have \\(\\E(\\nu'\\circ w_6)=0\\), but \\(\\E:\\pi_{11}^3=\\Z_2\\epsilon_3\\rightarrow\\pi_{12}^4=\\Z_2\\epsilon_4\\) is an isomorphism, so \\(\\nu'\\circ w_6=0\\). "
):

AddRelation(
 o(E(nuprime),nubar[7]),
 true,
 o(epsilon[4],nu[12]),
 "Suspension of Toda's Equations 7.12"
):

AddRelation(
 o(epsilonprime,eta[13]),
 true,
 o(nuprime,epsilon[6]),
 "Toda, Equations 7.12"
):

AddRelation(
 o(E(epsilonprime),eta[14]),
 true,
 o(E(nuprime),epsilon[7]),
 "Toda, Equations 7.12"
):

AddRelation(
 o(nu[5],E(sigmaprime),eta[15]),
 true,
 0,
 "If \\(2y=0\\) and \\(y\\) is a suspension then \\((2x)\\circ y)=2(x\\circ y)=x\\circ(2y)=0\\). We have \\(\\nu_5\\circ\\E\\sigma'=2\\nu_5\\circ\\sigma_8\\), and \\(\\eta_{15}\\) is a suspension and \\(2\\eta_{15}=0\\).  It follows that \\(\\nu_5\\circ\\E\\sigma'\\circ\\eta_{15}=0\\). " 
):

AddRelation(
 o(nu[m_],epsilon[n_]),
 n_ = m_+3 and m_ >= 6,
 2 * o(nubar[m_],nu[m_+8]),
 "Toda, Equations 7.18"
):

AddRelation(
 o(nu[m_],nubar[n_]),
 n_ = m_+3 and m_ >= 6,
 2 * o(nubar[m_],nu[m_+8]),
 "Toda, Equations 7.17 and 7.18"
):

AddRelation(
 o(sigma[n_],nu[m_]),
 m_ = n_+7 and n_ >= 12,
 0,
 "Toda, Equations 7.20"
):

AddRelation(
 o(nu[n_],sigma[m_]),
 m_ = n_+3 and n_ >= 11,
 0,
 "Toda, Equations 7.20"
):

AddRelation(
 o(2 * eta[2],epsilon[3]),
 true,
 0,
 "Notes by Strickland"
):

AddRelation(
 o(2 * eta[2],mu[3]),
 true,
 0,
 "Notes by Strickland"
):

AddRelation(
 o(w[6],eta[11]),
 true,
 0,
 "Apply P to the relation \\(H(\\sigma')=\\eta_{13}\\) in Toda, Lemma 5.14 "
):

AddRelation(
 o(w[6],nu[11]),
 true,
 2 * nubar[6],
 "Notes by Strickland"
):

AddRelation(
 o(eta[7],E(sigmaprime)),
 true,
 0,
 "Suspend the relation \\(\\eta_6\\circ\\sigma'=4\\nubar_6\\)"
):

AddRelation(
 o(mu[n_],eta[m_]),
 m_ = n_+9 and n_ >= 3,
 o(eta[n_],mu[n_+1]),
 "Notes by Strickland"
):

AddRelation(
 o(E(nuprime),sigmaprime),
 true,
 2 * E(epsilonprime),
 "Notes by Strickland"
):

AddRelation(
 o(eta[4],eta[5],epsilon[6]),
 true,
 2 * E(epsilonprime),
 "Suspend the relation \\(\\eta_3\\circ\\eta_4\\circ\\epsilon_5=2\\epsilon'\\) given by Toda, Lemma 6.6 "
):

AddRelation(
 o(eta[8],eta[9],w[10]),
 true,
 0,
 "This is in \\(\\pi_{19}^8\\), which is in the stable range, but it is killed by one suspension (because \\(\\E w_{k}=0\\) for any \\(k\\)). "
):

AddRelation(
 o(nuprime,sigmasecond),
 true,
 0,
 "Notes by Strickland"
):

AddRelation(
 o(nu[6],mu[9]),
 true,
 8 * o(w[6],sigma[11]),
 "Toda, Equations 7.25"
):

AddRelation(
 o(w[6],nubar[11]),
 true,
 0,
 "Toda, Equations 7.27"
):

AddRelation(
 o(w[6],epsilon[11]),
 true,
 0,
 "Toda, Equations 7.27"
):

AddRelation(
 o(w[12],eta[23]),
 true,
 E(thetaprime),
 "Toda, Equations 7.30"
):

AddRelation(
 o(nu[7],zeta[10]),
 true,
 4 * o(sigmaprime,sigma[14]),
 "Toda, Lemma 9.2"
):

AddRelation(
 o(nu[6],zeta[9]),
 true,
 2 * o(sigmasecond,sigma[13]),
 "Toda, Equations 10.7"
):

AddRelation(
 o(E(theta),eta[25],eta[26]),
 true,
 8 * o(sigma[13],sigma[20]),
 "We have \\(\\E\\theta=P(\\iota_{27})=w_{13}\\) by Toda's Equations 7.30, so \\((\\E\\theta)\\circ\\eta_{25}\\circ\\eta_{26}=P(\\eta_{25}\\circ\\eta_{26})\\), and this is the same as \\(8\\sigma_{13}\\circ\\sigma_{20}\\) by Toda's Equations 10.10."
):

AddRelation(
 o(w[14],eta[27]),
 true,
 4 * o(sigma[14],sigma[21]),
 "Toda, Equations 10.10"
):

AddRelation(
 o(eta[9],eta[10],mu[11]),
 true,
 4 * zeta[9],
 "Toda, Equations 10.12"
):

AddRelation(
 o(E(nuprime),kappa[7]),
 true,
 E(epsilonbarprime),
 "Toda, Lemma 12.3"
):

AddRelation(
 o(epsilon[n_],epsilon[m_]),
 m_ = n_+8 and n_ >= 3,
 o(eta[n_],epsilonbar[n_+1]),
 "Toda, Equations 12.4"
):

AddRelation(
 o(epsilon[n_],nubar[m_]),
 m_ = n_+8 and n_ >= 3,
 o(eta[n_],epsilonbar[n_+1]),
 "Toda, Equations 12.4"
):


AddRelation(
 o(epsilon[n_],sigma[m_]),
 m_ = n_+8 and n_ >= 3,
 0,
 "Toda, Lemma 10.7"
):

AddRelation(
 o(epsilonbar[n_],eta[m_]),
 m_ = n_+15 and n_ >= 3,
 o(eta[n_],epsilonbar[n_+1]),
 "Toda, Equations 12.4"
):

AddRelation(
 o(eta[12],rho[13]),
 true,
 o(sigma[12],mu[19]),
 "Toda, Proposition 12.20(i)"
):

AddRelation(
 o(eta[3],eta[4],epsilonbar[5]),
 true,
 2 * epsilonbarprime,
 "Toda, Lemma 12.3"
):

AddRelation(
 o(eta[3],eta[4],mubar[5]),
 true,
 2 * mubarprime,
 "Toda, Lemma 12.4"
):

AddRelation(
 o(eta[n_],kappa[m_]),
 m_ = n_+1 and n_ >= 6,
 epsilonbar[n_],
 "Toda, Equations 10.23"
):

AddRelation(
 o(eta[n_],rho[m_]),
 m_=n_+1 and n_>=13,
 o(sigma[n_],mu[n_+7]),
 "Toda, Proposition 12.20(i)"
):

AddRelation(
 o(kappa[n_],eta[m_]),
 m_ = n_+14 and n_ >= 9,
 epsilonbar[n_],
 "Toda, Equations 10.23"
):

AddRelation(
 o(mu[n_],sigma[m_]),
 m_=n_+9 and n_>=13,
 o(sigma[n_],mu[n_+7]),
 "Toda, Proposition 12.20(i)"
):

AddRelation(
 o(nu[n_],sigma[m_],nu[p_],nu[q_]),
 m_=n_+3 and p_=n_+10 and q_=n_+13 and n_>=5,
 o(eta[n_],epsilonbar[n_+1]),
 "Toda, Equations 12.4"
):

AddRelation(
 o(nubar[n_],sigma[m_]),
 m_ = n_+8 and n_ >= 6,
 0,
 "Toda, Lemma 10.7"
):

AddRelation(
 o(rho[n_],eta[m_]),
 o(sigma[n],mu[n+7]),
 m_=n_+16 and n_>=13,
 "Toda, Proposition 12.20(i)"
):

AddRelation(
 o(sigma[10],nubar[17]),
 true,
 o(sigma[10],epsilon[17]),
 "Toda, Equations 10.18"
):

AddRelation(
 o(sigma[13],zeta[20]),
 true,
 0,
 "Toda, Equations 12.23"
):

AddRelation(
 o(sigma[n_],epsilon[m_]),
 m_ = n_+7 and n_ >= 11,
 0,
 "Toda, Lemma 10.7"
):

AddRelation(
 o(sigma[n_],nubar[m_]),
 m_ = n_+7 and n_ >= 11 ,
 0,
 "Toda, Equations 10.18"
):

AddRelation(
 o(w[14],nu[27],nu[30]),
 true,
 2 * o(omega[14],nu[30]),
 "Toda, Equations 12.27"
):

AddRelation(
 o(sigmaprime,eta[14],epsilon[15]),
 true,
 E(zetaprime),
 "Toda, Lemma 12.1 (noting that \\(2\\pi_{23}^{7}=0\\))"
):

AddRelation(
 o(E(sigmaprime),eta[15],epsilon[16]),
 true,
 E(zetaprime),
 "Toda, Lemma 12.1 (noting that \\(2\\pi_{23}^{7}=0\\))"
):

AddRelation(
 o(eta[5],w[6]),
 true,
 0,
 "\\(\\eta_5\\circ w_6\\) lies in the kernel of the map \\(\\E:\\pi_{11}^5\\rightarrow\\pi_{12}^6\\), which is zero by inspection of Toda's Proposition 5.11"
):

AddRelation(
 o(eta[5],nubar[6]),
 true,
 o(nu[5],nu[8],nu[11]),
 "This holds after one suspension by Toda's Lemma 6.3, but the map \\(\\E:\\pi_{14}^5\\rightarrow\\pi_{15}^6\\) is injective by Toda's Theorem 7.2."
):

AddRelation(
 o(eta[3],E(muprime)),
 true,
 0,
 "We find by calculation that \\(H:\\pi_{15}^3\\rightarrow\\pi_{15}^5\\) is injective, so \\(\\E:\\pi_{14}^2\\rightarrow\\pi_{15}^3\\) must be zero.  In particular \\({\\eta_3}\\circ\\E\\mu'=\\E(\\eta_2\\circ\\mu')=0\\)."
):

AddRelation(
 o(eta[3],epsilon[4],nu[12]),
 true,
 0,
 "One checks that \\(H(\\eta_3\\circ\\epsilon_4\\circ\\nu_{12}=0\\), but one can also calculate the Hopf invariants of Toda's generators to see that \\(H:\\pi_{15}^3\\rightarrow\\pi_{15}^5\\) is injective."
):

AddRelation(
 o(eta[3],E(epsilonbarprime)),
 true,
 0,
 "We have \\(\\E{\\epsilonbar'}=(\\E\\nu')\\circ\\kappa_7\\) by Toda's Lemma 12.3, and \\(\\eta_3\\circ\\E\\nu'=0\\) by Toda's Lemma 5.7, so \\(\\eta_3\\circ\\E{\\epsilonbar'}=0\\). "
):

AddRelation(
 o(nu[5],sigma[8],eta[15]),
 true,
 Coset[o(nu[5],epsilon[8]),{4 * zeta[5]}],
 "Notes by Strickland, cor-nu-sigma-eta"
):

AddRelation(
 o(nu[n_],nu[m_],nu[p_],nu[q_]), 
 m_ = n_+3 and p_ = m_+3 and q_ = p_+3 and n_ >= 6,
 0,
 "\\({\\nu_n}\\circ{\\nu_{n+3}}\\circ{\\nu_{n+6}}\\circ{\\nu_{n+9}}=0\\) for \\(n \\geq 6)",
 "Notes by Strickland, prop-nu-nu-nu-nu"
):

AddRelation(
 o(nu[5],nu[8],sigma[11]),
 true,
 0,
 "Notes by Strickland, prop-nu-nu-sigma"
):

AddRelation(
 o(epsilonprime,nu[13]),
 true,
 0,
 "Notes by Strickland, prop-epsilonprime-nu"
):

AddRelation(
 o(E(epsilonprime),nu[14]),
 true,
 0,
 "Notes by Strickland, prop-epsilonprime-nu"
):

AddRelation(
 o(nu[6],nubar[9]),
 true,
 2 * o(nubar[6],nu[14]),
 "Notes by Strickland, prop-nu-nubar"
):

AddRelation(
 o(nubar[10],nu[18]),
 true,
 0,
 "Notes by Strickland, prop-nubar-nu"
):

AddRelation(
 o(sigmathird,epsilon[12]),
 true,
 0,
 "Notes by Strickland, prop-sigmathird-epsilon"
):

AddRelation(
 o(sigmathird,nubar[12]),
 true,
 0,
 "Notes by Strickland, prop-sigmathird-nubar"
):

AddRelation(
 o(sigmasecond,epsilon[13]),
 true,
 0,
 "Notes by Strickland, prop-sigmasecond-epsilon"
):

AddRelation(
 o(sigmasecond,nubar[13]),
 true,
 0,
 "Notes by Strickland, prop-sigmasecond-nubar"
):

AddRelation(
 o(E(theta),nu[25]),
 true,
 0,
 "Toda, Equations 10.21 and 7.30"
):

AddRelation(
 o(nu[n_],epsilonbar[m_]),
 m_ = n_+3 and n_>=6,
 0,
 "\\(\\nu_n\\circ\\epsilonbar_{n+3}=0\\) for \\(n\\geq 6\\)",
 "\\(\\nu_5\\circ\\epsilonbar_8=\\nu_5\\circ\\eta_8\\circ\\kappa_9=w_5\\circ\\kappa_9\\) by Toda's Equations 5.10 and 10.23.  The claim follows by suspending."
):

AddRelation(
 o(w[10],eta[19]),
 true,
 2 * o(sigma[10],nu[17]),
 "Toda, Equations 7.21"
):

AddRelation(
 o(sigma[n_],nu[m_]),
 m_ = n_+7 and n_ >= 12,
 0,
 "\\(\\sigma_n\\circ\\nu_{n+7}=0\\) for \\(n\\geq 12\\)",
 "Toda, Equations 7.20"
):

AddRelation(
 o(nu[n_],sigma[m_]),
 m_ = n_+3 and n_ >= 11,
 0,
 "\\(\\nu_n\\circ\\sigma_{n+3}=0\\) for \\(n\\geq 11\\)",
 "Toda, Equations 7.20"
):

AddRelation(
 o(E(sigmaprime),nu[15],nu[18]),
 true,
 o(nu[8],sigma[11],nu[18]),
 "Notes by Strickland, prop-sigmaprime-nu-nu"
):

AddRelation(
 o(eta[n_],epsilonbar[m_]),
 m_ = n_+1 and n_ >= 10,
 0,
 "WHY IS THIS?"
):

UnknownComposites := {
o(eta[9], w[10]),
o(w[10], eta[19]), 
o(sigmaprime,nu[14]),
o(sigmasecond,nu[13]),
o(sigmathird,nu[12]),
o(nu[7], nubar[10]),
o(nu[9], sigma[12]),
o(nubar[10], nu[18]), 
o(E(sigmaprime), nu[15]), 
o(nu[5], sigma[8], eta[15])
}:

######################################################################

# Hopf invariants                                                      

AddRelation(
 H(eta[2]),
 true,
 iota[3],
 "Definition of \\(\\eta_2\\) (Toda, Chapter V)"
):

AddRelation(
 H(nu[4]),
 true,
 iota[7],
 "Definition of \\(\\nu_4\\) (Toda, Lemma 5.4)"
):

AddRelation(
 H(sigma[8]),
 true,
 iota[15],
 "Definition of \\(\\sigma_8\\) (Toda, Lemma 5.14)"
):

AddRelation(
 H(nuprime),
 true,
 eta[5],
 "Toda, Equations 5.3"
):

AddRelation(
 H(sigmathird),
 true,
 4 * nu[9],
 "Toda, Lemma 5.14"
):

AddRelation(
 H(sigmasecond),
 true,
 o(eta[11],eta[12]),
 "Toda, Lemma 5.14"
):

AddRelation( 
 H(sigmaprime),
 true,
 eta[13],
 "Toda, Lemma 5.14"
):

AddRelation(
 H(epsilon[3]),
 true,
 o(nu[5],nu[8]),
 "Toda, Lemma 6.1"
):

AddRelation(
 H(nubar[6]),
 true,
 nu[11],
 "For us this is part of the definition of \\(\\nubar_6\\).  Toda's Lemma 6.2 says that it is true modulo \\(2\\nu_{11}\\), which is part of the validation of our definition. "
):

AddRelation(
 H(mu[3]),
 true,
 sigmathird,
 "Toda, Lemma 6.5"
):

AddRelation(
 H(epsilonprime),
 true,
 epsilon[5],
 "Toda, Lemma 6.6"
):

AddRelation(
 H(muprime),
 true,
 mu[5],
 "Toda, beginning of Section VII(ii)"
):

AddRelation(
 H(zeta[5]),
 true,
 8 * sigma[9],
 "Toda, Lemma 6.7"
):

AddRelation(
 H(thetaprime),
 true,
 o(eta[21],eta[22]),
 "Toda, Lemma 7.5"
):

AddRelation(
 H(theta),
 true,
 eta[23],
 "Toda, Lemma 7.5"
):

AddRelation(
 H(epsilonbar[3]),
 true,
 o(nu[5],sigma[8],nu[15]),
 "Strickland, prop-hopf-epsilonbar"
):

AddRelation(
 H(epsilonstar[12]),
 true,
 o(nu[23],nu[26]),
 "Toda, Lemma 12.15"
):

AddRelation(
 H(lambda),
 true,
 o(nu[25],nu[28]),
 "Toda, Lemma 12.18"
):

AddRelation(
 H(lambdaprime),
 true,
 Coset(epsilon[21],{nubar[21]+epsilon[21]}),
 "Toda, Lemma 12.19"
):

AddRelation(
 H(lambdasecond),
 true,
 Coset(o(eta[19],epsilon[20]),{o(eta[19],epsilon[20])+o(nu[19],nu[22],nu[25])}),
 "Toda, Lemma 12.19"
):

AddRelation(
 H(mubar[3]),
 true,
 rhofourth,
 "Toda, Lemma 12.2"
):

AddRelation(
 H(mubarprime),
 true,
 Coset(mubar[5],Zap[E(E(E(Generators[SpherePi[19,2]])))]),
 "Toda, Lemma 12.4"
):

AddRelation(
 H(omega[14]),
 true,
 nu[27],
 "Toda, Lemma 12.15"
):

AddRelation(
 H(omegaprime),
 true,
 Coset(epsilon[23],{nubar[23] + epsilon[23]}),
 "Toda, Lemma 12.21"
):

AddRelation(
 H(rho(13)),
 true,
 4 * nu[25],
 "Toda, Equations 10.22"
):

AddRelation(
 H(rhofourth),
 true,
 4 * zeta[9],
 "Toda, Equations 10.12"
):

AddRelation(
 H(rhoprime),
 true,
 8 * sigma[17],
 "Toda, Equations 10.12"
):

AddRelation(
 H(rhosecond),
 true,
 mu[13],
 "This is part of our definition of \\(\\rho''\\) - see the notes by Strickland, prop-rho-second, and Toda, Equations 10.12"
):

AddRelation(
 H(rhothird),
 true,
 o(eta[11],mu[12]),
 "Toda, Equations 10.12"
):

AddRelation(
 H(sigmabar[6]),
 true,
 Coset(o(sigma[11],sigma[18]), {2 * o(sigma[11],sigma[18])}),
 "Toda, Lemma 12.5"
):

AddRelation(
 H(xiprime),
 true,
 nubar[21] + epsilon[21],
 "Toda, Lemma 12.19"
):

AddRelation(
 H(xisecond),
 true,
 o(eta[19],epsilon[20])+o(nu[19],nu[22],nu[25]),
 "Toda, Lemma 12.19"
):

AddRelation(
 H(zetabar[5]),
 true,
 8 * rhoprime,
 "Toda, Lemma 12.4"
):

AddRelation(
 H(zetaprime),
 true,
 zeta[11],
 "This is part of our definition of \\(\\zeta'\\), which is validated in the notes by Strickland, prop-zetaprime, which refines Toda's Lemma 12.1"
):

AddRelation(
 H(etastarprime),
 true,
 o(eta[29],eta[30]),
 "Toda, Lemma 12.14"
):

AddRelation(
 H(etastar[16]),
 true,
 eta[31],
 "Toda, Lemma 12.14"
):

AddRelation(
 H(epsilonbarprime),
 true,
 Coset(epsilonbar[5],{rhofourth}),
 "Notes by Strickland, prop-H-epsilonbarprime"
):

AddRelation(
 H(WhiteheadP(E(theta))),
 true,
 thetaprime,
 "Toda, Lemma 12.11"
):

AddRelation(
 H(kappa[7]),
 true,
 epsilon[13],
 "Notes by Strickland, prop-H-kappa"
):

######################################################################

# The Whitehead map                                                    

AddRelation(
 WhiteheadP(eta[3]),
 true,
 0,
 "\\(P(\\eta_3)\\) lies in the trivial group \\(\\pi_2S^1\\)."
):

AddRelation(
 WhiteheadP(eta[9]),
 true,
 o(E(nuprime),eta[7]),
 "Notes by Strickland"
):

AddRelation( 
 WhiteheadP(nu[5]),
 true,
 o(eta[2],nuprime),
 "Toda, Lemma 5.7; we have fudged the sign."
):

AddRelation(
 WhiteheadP(o(nu[5],sigma[8])),
 true,
 o(eta[2],epsilonprime),
 "Notes by Strickland, Proposition 2; we have fudged the sign"
):

AddRelation(
 WhiteheadP(sigmaprime),
 true,
 0,
 "Notes by Strickland, Proposition 3"
):

AddRelation(
 WhiteheadP(sigma[9]),
 true,
 Coset(o(nu[4],sigmaprime) - E(epsilonprime), {2(o(nu[4],sigmaprime) - E(epsilonprime))}),
 "Notes by Strickland.  We have fudged a sign."
):

AddRelation(
 WhiteheadP(sigma[11]),
 true,
 o(nu[5],nubar[8]) + o(nu[5],epsilon[8]),
 "Toda, Equations 7.17"
):

AddRelation(
 WhiteheadP(o(sigma[9],eta[16])),
 true,
 o(nu[4],sigmaprime,eta[14]) + o(E(nuprime),epsilon[7]),
 "Toda, Equations 7.16"
):

AddRelation(
 WhiteheadP(o(sigma[9],eta[16],eta[17])),
 true,
 o(nu[4],sigmaprime,eta[14],eta[15]) + o(E(nuprime),eta[7],epsilon[8]),
 "Toda, Equations 7.16"
):

AddRelation(
 WhiteheadP(nuprime),
 true,
 0,
 "To Do: Find this reference!"
):

AddRelation(
 WhiteheadP(epsilon[3]),
 true,
 0,
 "Takes place in \\(\\pi_9S^1=0\\)."
):

AddRelation(
 WhiteheadP(o(eta[3],epsilon[4])),
 true,
 0,
 "Takes place in \\(\\pi_{10}S^1=0\\)."
):

AddRelation(
 WhiteheadP(mu[3]),
 true,
 0,
 "Takes place in \\(\\pi_{10}S^1=0\\)."
):

AddRelation(
 WhiteheadP(o(eta[3],mu[4])),
 true,
 0,
 "Takes place in \\(\\pi_{11}S^1=0\\)."
):

AddRelation(
 WhiteheadP(epsilonprime),
 true,
 0,
 "Takes place in \\(\\pi_{11}S^1=0\\)."
):

AddRelation(
 WhiteheadP(muprime),
 true,
 0,
 "Takes place in \\(\\pi_{12}S^1=0\\)."
):

AddRelation(
 WhiteheadP(o(epsilon[3],nu[11])),
 true,
 0,
 "Takes place in \\(\\pi_{12}S^1=0\\)."
):

AddRelation(
 WhiteheadP(o(nuprime,epsilon[6])),
 true,
 0,
 "Takes place in \\(\\pi_{12}S^1=0\\)."
):

AddRelation(
 WhiteheadP(epsilonbar[3]),
 true,
 0,
 "Takes place in \\(\\pi_{16}S^1=0\\)."
):

AddRelation(
 WhiteheadP(o(eta[3],epsilonbar[4])),
 true,
 0,
 "Takes place in \\(\\pi_{17}S^1=0\\)."
):

AddRelation(
 WhiteheadP(sigmathird),
 true,
 0,
 "Takes place in \\(\\pi_{10}S^2=0\\)."
):

AddRelation(
 WhiteheadP(nubar[7]),
 true,
 0,
 "Notes by Strickland"
):

AddRelation(
 WhiteheadP(rhosecond),
 true,
 0,
 "\\(P(\\rho'')\\) lies in the kernel of \\(\\E:\\pi_{20}^{3}\\rightarrow\\pi_{21}^{4}\\), which is trivial by inspection of Toda's Theorem 12.7"
):

AddRelation(
 WhiteheadP(zeta[5]),
 true,
 Coset(o(eta[2],muprime),{2 * o(eta[2],muprime)}),
 "Notes by Strickland, prop-zeta"
):

AddRelation(
 WhiteheadP(epsilonbarprime),
 true,
 0,
 "This takes place in \\(\\pi_{18}^1=0\\)."
):

AddRelation(
 WhiteheadP(mubar[3]),
 true,
 0,
 "This takes place in \\(\\pi_{18}^1=0\\)."
):

AddRelation(
 WhiteheadP(o(eta[3],mubar[4])),
 true,
 0,
 "This takes place in \\(\\pi_{19}^1=0\\)."
):

AddRelation(
 WhiteheadP(rhofourth),
 true,
 0,
 "\\(P(\\rho^{(4)})=PH(\\mubar_3)=0\\) (using Toda, Lemma 12.2)"
):

AddRelation(
 o(nu[5],eta[8],epsilonbar[9]),
 true,
 0,
 "Toda, Equations 12.15 and 5.10"
):

AddRelation(
 WhiteheadP(E(E(rhoprime))),
 true,
 0,
 "Toda, Equations 12.15"
):

AddRelation(
 o(nu[5],eta[8],rhoprime),
 true,
 0,
 "Toda, Equations 12.15 gives \\(P(\\E^2\\rho')=0\\), but \\(P(\\E^2\\rho')=P(\\iota_{11})\\circ\\rho'=\\nu_5\\circ\\eta_8\\circ\\rho'\\) by Equations 5.10."
):

AddRelation(
 w[1],
 true,
 0,
 "\\(w_1=P(\\iota_3)=PH(\\eta_2)=0\\)"
):

AddRelation(
 w[2]  ,
 true,
 2 * eta[2],
 "Toda's Proposition 5.1 should say that \\(w_2=P(\\iota_5)=\\pm 2\\eta_2\\). In fact it says that \\(w_2=P(\\iota_5)=\\pm 2\\eta_3\\), but this is not dimensionally correct and is a typo.  We have fudged the sign ambiguity. "
):

AddRelation(
 w[3],
 true,
 0,
 "\\(w_3=P(\\iota_7)=PH(\\nu_4)=0\\)"
):

AddRelation(
 w[4],
 true,
 2 * nu[4] - E(nuprime),
 "Toda, Equations 5.8 say that \\(w_4=\\pm(2\\nu_4-\\E\\nu')\\). We have fudged the sign. "
):

AddRelation(
 w[5],
 true,
 o(nu[5],eta[8]),
 "Toda, Equations 5.10"
):

AddRelation(
 w[7],
 true,
 0,
 "Toda, Lemma 5.14 gives \\(w_7=P(\\iota_{15})=PH(\\sigma_8)=0\\)."
):

AddRelation(
 w[8],
 true,
 2 * sigma[8] - E(sigmaprime),
 "Toda, Equations 5.16 say that \\(w_8=\\pm(2\\sigma_8-\\E\\sigma')\\). We have fudged the sign. "
):

AddRelation(
 w[9],
 true,
 o(sigma[9],eta[16]) + nubar[9] + epsilon[9],
 "Toda, Equations 7.1"
):

AddRelation(
 w[11],
 true,
 o(sigma[11],nu[18]),
 "Toda, Equations 7.21"
):

AddRelation(
 w[13],
 true,
 E(theta),
 "Toda, Equations 7.30"
):

AddRelation(
 w[15],
 true,
 2 * o(sigma[15],sigma[22]),
 "Toda, Equations 10.10"
):

SpherePi := proc(n,m)
 local stem,is_stable,G;
 stem := n-m;
 is_stable := evalb(m>stem+1);

 if stem<0 or m<=0 or (n>1 and m=1) then
  return(Group());
 elif stem=0 then
  return(Group([],[x[n,[]]]));
 else
  return('SpherePi'(n,m));
 fi;
end:

# Nonpositive stems
for i from 1 to 20 do
 for j from 1 to i-1 do
  SpherePi(j,i) := []:
 od:
 SpherePi(i,i) := [[infinity,iota[i]]]:
od:

# Homotopy groups of the circle
for i from 2 to 20 do
 SpherePi(i,1) := []:
od:

# 1-stem
SpherePi(3,2) := [[infinity,eta[2]]]:

for i from 3 to 20 do
 SpherePi(i+1,i) := [[2,eta[i]]]:
od:

# 2-stem
for i from 2 to 20 do
 SpherePi(i+2,i) := [[2,o(eta[i+1],eta[i])]]:
od:

# 3-stem
SpherePi(5,2) := [[2,o(eta[2],eta[3],eta[4])]]:

# NB nuprime is usually only defined at p=2. 
# Presumably we get a generator from the unstable J-map?
SpherePi(6,3) := [[4,nuprime]]: 

SpherePi(7,4) := [[infinity,nu[4]],[4,E(nuprime)]]:

for i from 5 to 20 do 
 SpherePi(i+3,i) := [[8,nu[i]]]:
od:

# 4-stem
SpherePi(6,2) := [[4,o(eta[2],nuprime)]]:
SpherePi(7,3) := [[2,o(nuprime,eta[6])]]:
SpherePi(8,4) := [[2,o(nu[4],eta[7])],[2,o(E(nuprime),eta[7])]]:
SpherePi(9,5) := [[2,o(nu[5],eta[8])]]:

for i from 6 to 20 do
 SpherePi(i+4,i) := []:
od:

# 5-stem

SpherePi(7, 2) := [[2,o(eta[2],nuprime,eta[6])]]:
SpherePi(8, 3) := [[2,o(nuprime,eta[6],eta[7])]]:
SpherePi(9, 4) := [[2,o(nu[4],eta[7],eta[8])],
                   [2,o(E(nuprime),eta[7],eta[8])]]:
SpherePi(10, 5) := [[2,o(nu[5],eta[8],eta[9])]]:
SpherePi(11, 6) := [[infinity,w[6]]]:

for i from 7 to 20 do 
 SpherePi(i+5,i) := []:
od:

# 6-stem

SpherePi(8, 2) := [[2,o(eta[2],nuprime,eta[6],eta[7])]]:
SpherePi(9, 3) := []:
SpherePi(10, 4) := [[8,o(nu[4],nu[7])],3]:

for i from 5 to 20 do
 SpherePi(i+6,i) := [[2,o(nu[i],nu[i+3])]]:
od:

# 7-stem

SpherePi( 9, 2) := []:
SpherePi(10, 3) := []:
SpherePi(11, 4) := []:
SpherePi(12, 5) := [[2,sigmathird]]:
SpherePi(13, 6) := [[4,sigmasecond]]:
SpherePi(14, 7) := [[8,sigmaprime]]:
SpherePi(15, 8) := [[infinity,sigma[8]],[8,E(sigmaprime)]]:

for i from 9 to 20 do
 SpherePi(i+7,i) := [[16,sigma[i]]]:
od:

# 8-stem

SpherePi(10, 2) := []:
SpherePi(11, 3) := [[2,epsilon[3]]]:
SpherePi(12, 4) := [[2,epsilon[4]]]:
SpherePi(13, 5) := [[2,epsilon[5]]]:
SpherePi(14, 6) := [[2,epsilon[6]],[24,nubar[6]]]:
SpherePi(15, 7) := [[2,epsilon[7]],[2,nubar[7]],[2,o(sigmaprime,eta[14])]]:
SpherePi(16, 8) := [[2,epsilon[8]],
                    [2,nubar[8]],
                    [2,o(E(sigmaprime),eta[15])],
                    [2,o(sigma[8],eta[15])]]:
SpherePi(17, 9) := [[2,epsilon[9]],
                    [2,nubar[9]],
                    [2,o(sigma[9],eta[16])]]:

for i from 10 to 20 do
 SpherePi(i+8,i) := [[2,epsilon[i]],[2,nubar[i]]]:
od:

# 9-stem

SpherePi(11, 2) := [[2,o(eta[ 2],epsilon[ 3])]]:
SpherePi(12, 3) := [[2,o(eta[ 3],epsilon[ 4])],
                    [2,mu[ 3]]]:
SpherePi(13, 4) := [[2,o(eta[ 4],epsilon[ 5])],
                    [2,mu[ 4]],
                    [2,o(nu[ 4],nu[ 7],nu[10])] ]:
SpherePi(14, 5) := [[2,o(eta[ 5],epsilon[ 6])],
                    [2,mu[ 5]],
                    [2,o(nu[ 5],nu[ 8],nu[11])] ]:
SpherePi(15, 6) := [[2,o(eta[ 6],epsilon[ 7])],
                    [2,mu[ 6]],
                    [2,o(nu[ 6],nu[ 9],nu[12])] ]:
SpherePi(16, 7) := [[2,o(eta[ 7],epsilon[ 8])],
                    [2,mu[ 7]],
                    [2,o(nu[ 7],nu[10],nu[13])],
                    [2,o(sigmaprime,eta[14],eta[15])] ]:
SpherePi(17, 8) := [[2,o(eta[ 8],epsilon[ 9])],
                    [2,mu[ 8]],
                    [2,o(nu[ 8],nu[11],nu[14])],
                    [2,o(E(sigmaprime),eta[15],eta[16])],
                    [2,o(sigma[8],eta[15],eta[16])] ]:
SpherePi(18, 9) := [[2,o(eta[ 9],epsilon[10])],
                    [2,mu[ 9]],
                    [2,o(nu[ 9],nu[12],nu[15])],
                    [2,o(sigma[9],eta[16],eta[17])] ]:
SpherePi(19, 10) := [[2,o(eta[10],epsilon[11])],
                     [2,mu[10]],
                     [2,o(nu[10],nu[13],nu[16])],
                     [infinity,w[10]]]:

for i from 11 to 20 do
 SpherePi(i+9,i) := [[2,o(eta[n],epsilon[n+1])],
                     [2,mu[n]],
                     [2,o(nu[n],nu[n+3],nu[n+6])]]:
od:

# 10-stem

SpherePi(12, 2) := [[2,o(eta[ 2],mu[ 3])],
                    [2,o(eta[ 2],eta[ 3],epsilon[4])]]:
SpherePi(13, 3) := [[2,o(eta[ 3],mu[ 4])],
                    [4,epsilonprime]]:
SpherePi(14, 4) := [[2,o(eta[ 4],mu[ 5])],
                    [4,E(epsilonprime)],
                    [8,o(nu[ 4],sigmaprime)] ]:
SpherePi(15, 5) := [[2,o(eta[ 5],mu[ 6])],
                    [8,o(nu[ 5],sigma[ 8])] ]:
SpherePi(16, 6) := [[2,o(eta[ 6],mu[ 7])],
                    [8,o(nu[ 6],sigma[ 9])]]:
SpherePi(17, 7) := [[2,o(eta[ 7],mu[ 8])],
                    [8,o(nu[ 7],sigma[10])]]:
SpherePi(18, 8) := [[2,o(eta[ 8],mu[ 9])],
                    [8,o(nu[ 8],sigma[11])],
                    [8,o(sigma[ 8],nu[15])]]:
SpherePi(19, 9) := [[2,o(eta[ 9],mu[10])],
                    [8,o(sigma[ 9],nu[16])]]:
SpherePi(20, 10) := [[2,o(eta[10],mu[11])],
                     [4,o(sigma[10],nu[17])]]:
SpherePi(21, 11) := [[2,o(eta[11],mu[12])],
                     [2,o(sigma[11],nu[18])]]:

for i from 12 to 20 do
 SpherePi(i+10,i) := [[2,o(eta[i],mu[i+1])]]:
od:

# 11-stem

SpherePi(13, 2) := [[4,o(eta[2],epsilonprime)],
                    [2,o(eta[2],eta[3],mu[4])]]:
SpherePi(14, 3) := [[4,muprime],
                    [2,o(epsilon[3],nu[11])],
                    [2,o(nuprime,epsilon[6])]]:
SpherePi(15, 4) := [[4,E(muprime)],
                    [2,o(epsilon[4],nu[12])],
                    [2,o(E(nuprime),epsilon[7])],
                    [2,o(nu[ 4],sigmaprime,eta[14])],
                    [2,o(nu[ 4],nubar[7])],
                    [2,o(nu[ 4],epsilon[7])]]:
SpherePi(16, 5) := [[2,o(nu[ 5],nubar[8])],
                    [2,o(nu[ 5],epsilon[8])],
                    [8,zeta[ 5]]]:
SpherePi(17, 6) := [[8,zeta[ 6]],
                    [4,o(nubar[ 6],nu[14])]]:
SpherePi(18, 7) := [[8,zeta[ 7]],
                    [2,o(nubar[ 7],nu[15])]]:
SpherePi(19, 8) := [[8,zeta[ 8]],
                    [2,o(nubar[ 8],nu[16])]]:
SpherePi(20, 9) := [[8,zeta[ 9]],
                    [2,o(nubar[ 9],nu[17])]]:
SpherePi(21, 10) := [[8,zeta[10]]]:
SpherePi(22, 11) := [[8,zeta[11]]]:
SpherePi(23, 12) := [[8,zeta[12]],
                     [infinity,w[12]]]:

for i from 13 to 20 do 
 SpherePi(i+11,i) := [8,zeta[i]]:
od:

# 12-stem

# Here Toda lists o(eta[2],nuprime,nubar[6]) as a generator, but this  
# is the same as o(eta[2],epsilon[3],nu[11]) by his Equations 7.12,    
# and that is a more convenient expression for comparison with other   
# results.
                                                   
SpherePi(14, 2) :=  [
   o(eta[2],muprime),
   o(eta[2],epsilon[3],nu[11]),
   o(eta[2],nuprime,epsilon[6])
  ]:

SpherePi(15, 3) :=  [
   o(nuprime,mu[6]),
   o(nuprime,eta[6],epsilon[7])
  ]:

SpherePi(16, 4) :=  [
   o(nu[4],sigmaprime,eta[14],eta[15]),
   o(nu[4],nu[7],nu[10],nu[13]),
   o(nu[4],mu[7]),
   o(nu[4],eta[7],epsilon[8]),
   o(E(nuprime),mu[7]),
   o(E(nuprime),eta[7],epsilon[8])
  ]:

SpherePi(17, 5) :=  [
   o(nu[5],nu[8],nu[11],nu[14]),
   o(nu[5],mu[8]),
   o(nu[5],eta[8],epsilon[9])
  ]:

SpherePi(18, 6)  [o(w[6],sigma[11])]:
SpherePi(19, 7) := []:
SpherePi(20, 8) := []:
SpherePi(21, 9) := []:
SpherePi(22, 10)  [o(w[10],nu[19])]:
SpherePi(23, 11)  [thetaprime]:
SpherePi(24, 12)  [theta,E(thetaprime)]:
SpherePi(25, 13)  [E(theta)]:

for i from 13 to 20 do 
 SpherePi(12+i,i) := []:
od:

## 13-stem
#
#
#SpherePi(15, 2) : [:
#  o(eta[2],nuprime,mu[6]),
#  o(eta[2],nuprime,eta[6],epsilon[7])
# ]
#
#SpherePi(16, 3) : [:
#  o(nuprime,eta[6],mu[7])
# ]
#
#SpherePi(17, 4) : [:
#  o(nu[4],nu[7],sigma[10]),
#  o(nu[4],eta[7],mu[8]),
#  o(E(nuprime),eta[7],mu[8])
# ]
#
#SpherePi(18, 5) : [:
#  o(nu[5],sigma[ 8],nu[15]),
#  o(nu[5],eta[8],mu[9])
# ]
#
#SpherePi(19, 6) : [:
#  o(nu[6],sigma[ 9],nu[16])
# ]
#
#SpherePi(20, 7) : [:
#  o(nu[7],sigma[10],nu[17])
# ]
#
#SpherePi(21, 8) := [:
#   o(sigma[ 8],nu[15],nu[18]),
#   o(nu[8],sigma[11],nu[18])
#  ]
#
#SpherePi(22, 9) := [:
#   o(sigma[ 9],nu[16],nu[19])
#  ]
#
#SpherePi(23, 10) := [:
#   o(sigma[10],nu[17],nu[20])
#  ]
#
#SpherePi(24, 11) := [:
#   o(sigma[11],nu[18],nu[21]),
#   o(thetaprime,eta[23])
#  ]
#
#SpherePi(25, 12) := [:
#   o(theta,eta[24]),
#   o(E(thetaprime),eta[24])
#  ]
#
#SpherePi(26, 13) := [:
#   o(E(theta),eta[25])
#  ]
#
#SpherePi(27, 14) := [:
#   w[14]
#  ]
#
#SpherePi(k_, n_) : := []: /; k == n+13 && n>14
#
#
## 14-stem
#
#
#SpherePi(16, 2) :=  [:
#   o(eta[2],nuprime,eta[6],mu[7])
#  ]
#
#SpherePi(17, 3) :=  [:
#   o(epsilon[3],nu[11],nu[14])
#  ]
#
#SpherePi(18, 4) :=  [:
#   o(epsilon[4],nu[12],nu[15]),
#   o(nu[4],zeta[7]),
#   o(nu[4],nubar[7],nu[15])
#  ]
#
#SpherePi(19, 5) :=  [:
#   o(nu[5],zeta[8]),
#   o(nu[5],nubar[8],nu[16])
#  ]
#
#SpherePi(20, 6) :=  [:
#   o(sigmasecond,sigma[13]),
#   o(nubar[6],nu[14],nu[17])
#  ]
#
#SpherePi(21, 7) :=  [:
#   o(sigmaprime,sigma[14]),
#   kappa[7]
#  ]
#
#SpherePi(22, 8) :=  [:
#   o(sigma[8],sigma[15]),
#   o(E(sigmaprime),sigma[15]),
#   kappa[8]
#  ]
#
#SpherePi(23, 9) :=  [:
#   o(sigma[9],sigma[16]),
#   kappa[9]
#  ]
#
#SpherePi(24, 10) :=  [:
#   o(sigma[10],sigma[17]),
#   kappa[10]
#  ]
#
#SpherePi(25, 11) :=  [:
#   o(sigma[11],sigma[18]),
#   kappa[11]
#  ]
#
#SpherePi(26, 12) :=  [:
#   o(sigma[12],sigma[19]),
#   kappa[12],
#   o(w[12],nu[23])
#  ]
#
#SpherePi(27, 13) :=  [:
#   o(sigma[13],sigma[20]),
#   kappa[13]
#  ]
#
#SpherePi(28, 14) :=  [:
#   o(sigma[14],sigma[21]),
#   kappa[14]
#  ]
#
#SpherePi(29, 15) :=  [:
#   o(sigma[15],sigma[22]),
#   kappa[15]
#  ]
#
#SpherePi(k_, n_) : := [:
#   o(sigma[n],sigma[n+7]),
#   kappa[n]
#  ] /; k == n+14 && n>=16
#
## 15-stem
#
#
#
#
#SpherePi(17, 2) := [:
#   o(eta[2],epsilon[3],nu[11],nu[14])
#  ]
#
#SpherePi(18, 3) := [:
#   epsilonbar[3]
#  ]
#
#SpherePi(19, 4) := [:
#   epsilonbar[4]
#  ]
#
#SpherePi(20, 5) := [:
#   epsilonbar[5],
#   rhofourth
#  ]
#
#SpherePi(21, 6) := [:
#   epsilonbar[6],
#   rhothird
#  ]
#
#SpherePi(22, 7) := [:
#   epsilonbar[7],
#   rhosecond,
#   o(sigmaprime,nubar[14]),
#   o(sigmaprime,epsilon[14])
#  ]
#
#SpherePi(23, 8) := [:
#   epsilonbar[8],
#   E(rhosecond),
#   o(E(sigmaprime),nubar[15]),
#   o(E(sigmaprime),epsilon[15]),
#   o(sigma[8],nubar[15]),
#   o(sigma[8],epsilon[15])
#  ]
#
#SpherePi(24, 9) := [:
#   epsilonbar[9],
#   rhoprime,
#   o(sigma[9],nubar[16]),
#   o(sigma[9],epsilon[16])
#  ]
#
#SpherePi(25, 10) := [:
#   epsilonbar[10],
#   E(rhoprime),
#   o(sigma[10],nubar[17])
#  ]
#
#SpherePi(26, 11) := [:
#   epsilonbar[11],
#   E(E(rhoprime))
#  ]
#
#SpherePi(27, 12) := [:
#   epsilonbar[12],
#   E(E(E(rhoprime)))
#  ]
#
#SpherePi(n_, m_) : := [:
#   epsilonbar[m],
#   rho(m)
#  ] /; n === m+15 && m >= 13 && m =!= 16
#
#SpherePi(31, 16) := [:
#   epsilonbar[16],
#   rho(16),
#   w[16]
#  ]
#
## 16-stem
#
#
#
#SpherePi(18, 2) :=  [:
#   o(eta[2],epsilonbar[3])
#  ]
#
#SpherePi(19, 3) :=  [:
#   o(eta[3],epsilonbar[4]),
#   o(mu[3],sigma[12])
#  ]
#
#SpherePi(20, 4) :=  [:
#   o(eta[4],epsilonbar[5]),
#   o(mu[4],sigma[13]),
#   o(nu[4],nu[7],sigma[10],nu[17])
#  ]
#
#SpherePi(21, 5) :=  [:
#   o(eta[5],epsilonbar[6]),
#   o(mu[5],sigma[14])
#  ]
#
#SpherePi(22, 6) :=  [:
#   o(eta[6],epsilonbar[7]),
#   o(mu[6],sigma[15]),
#   zetaprime
#  ]
#
#SpherePi(23, 7) :=  [:
#   o(eta[7],epsilonbar[8]),
#   o(mu[7],sigma[16]),
#   E(zetaprime),
#   o(sigmaprime,mu[14])
#  ]
#
#SpherePi(24, 8) :=  [:
#   o(eta[8],epsilonbar[9]),
#   o(mu[8],sigma[17]),
#   E(E(zetaprime)),
#   o(sigma[8],nu[15],nu[18],nu[21]),
#   o(sigma[8],mu[15]),
#   o(sigma[8],eta[15],epsilon[16]),
#   o(E(sigmaprime),mu[15])
#  ]
#
#SpherePi(25, 9) :=  [:
#   o(mu[9],sigma[18]),
#   o(sigma[9],nu[16],nu[19],nu[22]),
#   o(sigma[9],mu[16]),
#   o(sigma[9],eta[16],epsilon[17])
#  ]
#
#SpherePi(26, 10) :=  [:
#   o(sigma[10],mu[17]),
#   o(w[10],sigma[19])
#  ]
#
#SpherePi(27, 11) :=  [ :
#   o(sigma[11],mu[18])
#  ]
#
#SpherePi(28, 12) :=  [:
#   o(sigma[12],mu[19])
#  ]
#
#SpherePi(29, 13) :=  [:
#   o(sigma[13],mu[20])
#  ]
#
#SpherePi(30, 14) :=  [:
#   o(sigma[14],mu[21]),
#   omega[14]
#  ]
#
#SpherePi(31, 15) :=  [:
#   o(sigma[15],mu[22]),
#   omega[15],
#   etastarprime
#  ]
#
#SpherePi(32, 16) :=  [:
#   o(sigma[16],mu[23]),
#   omega[16],
#   E(etastarprime),
#   etastar[16]
#  ]
#
#SpherePi(33, 17) :=  [:
#   o(sigma[17],mu[24]),
#   omega[17],
#   etastar[17]
#  ]
#
#SpherePi(k_, n_) : := [:
#   o(sigma[n],mu[n+7]),
#   omega[n]
#  ] /; k == n+16 && n>=18
#
## 17-stem
#
#
#
#SpherePi(19, 2) := [:
#  o(eta[2],mu[3],sigma[12]),
#  o(eta[2],eta[3],epsilonbar[4])
# ]
#
#SpherePi(20, 3) := [:
#  o(eta[3],mu[4],sigma[13]),
#  epsilonbarprime,
#  mubar[3]
# ]
#
#SpherePi(21, 4) := [:
#  o(eta[4],mu[5],sigma[14]),
#  E(epsilonbarprime),
#  mubar[4],
#  o(nu[4],sigmaprime,sigma[14]),
#  o(nu[4],kappa[7])
# ]
#
#SpherePi(22, 5) := [:
#  o(eta[5],mu[6],sigma[15]),
#  mubar[5],
#  o(nu[5],kappa[8])
# ]
#
#SpherePi(23, 6) := [:
#  o(eta[6],mu[7],sigma[16]),
#  mubar[6],
#  o(nu[6],kappa[9]),
#  WhiteheadP[E(theta)]
# ]
#
#SpherePi(24, 7) := [:
#  o(eta[7],mu[8],sigma[17]),
#  mubar[7],
#  o(nu[7],kappa[10]),
#  o(sigmaprime,eta[14],mu[15])
# ]
#
#SpherePi(25, 8) := [:
#  o(eta[8],mu[9],sigma[18]),
#  mubar[8],
#  o(nu[8],kappa[11]),
#  o(E(sigmaprime),eta[15],mu[16]),
#  o(sigma[8],eta[15],mu[16])
# ]
#
#SpherePi(26, 9) := [:
#  o(eta[9],mu[10],sigma[19]),
#  mubar[9],
#  o(nu[9],kappa[12]),
#  o(sigma[9],eta[16],mu[17])
# ]
#
#SpherePi(27, 10) := [:
#  mubar[10],
#  o(nu[10],kappa[13]),
#  o(sigma[10],eta[17],mu[18])
# ]
#
#SpherePi(28, 11) := [:
#  mubar[11],
#  o(nu[11],kappa[14]),
#  o(sigma[11],eta[18],mu[19])
# ]
#
#SpherePi(29, 12) := [:
#  mubar[12],
#  o(nu[12],kappa[15]),
#  o(sigma[12],eta[19],mu[20]),
#  epsilonstar[12]
# ]
#
#SpherePi(30, 13) := [:
#  mubar[13],
#  o(nu[13],kappa[16]),
#  o(sigma[13],eta[20],mu[21]),
#  epsilonstar[13]
# ]
#
#SpherePi(31, 14) := [:
#  mubar[14],
#  o(nu[14],kappa[17]),
#  o(sigma[14],eta[21],mu[22]),
#  epsilonstar[14]
# ]
#
#SpherePi(32, 15) := [:
#  mubar[15],
#  o(nu[15],kappa[18]),
#  o(sigma[15],eta[22],mu[23]),
#  epsilonstar[15],
#  o(etastarprime,eta[31])
# ]
#
#SpherePi(33, 16) := [:
#  mubar[16],
#  o(nu[16],kappa[19]),
#  o(sigma[16],eta[23],mu[24]),
#  epsilonstar[16],
#  o(E(etastarprime),eta[32]),
#  o(etastar[16],eta[32])
# ]
#
#SpherePi(34, 17) := [:
#  mubar[17],
#  o(nu[17],kappa[20]),
#  o(sigma[17],eta[24],mu[25]),
#  epsilonstar[17],
#  o(etastar[17],eta[33])
# ]
#
#SpherePi(35, 18) := [:
#  mubar[18],
#  o(nu[18],kappa[21]),
#  o(sigma[18],eta[25],mu[26]),
#  epsilonstar[18],
#  w[18]
# ]
#
#SpherePi(k_, n_) : := [:
#  mubar[n],
#  o(nu[n],kappa[n+3]),
#  o(sigma[n],eta[n+7],mu[n+8]),
#  epsilonstar[n]
# ] /; k == n+17 && n >= 19
#
#
## 18-stem
#
#
#
#
#SpherePi(20, 2) := [:
#  o(eta[2],mubar[3]),
#  o(eta[2],epsilonbarprime),
#  o(eta[2],eta[3],mu[4],sigma[13])
# ]
#
#SpherePi(21, 3) := [:
#  o(eta[3],mubar[4]),
#  o(muprime,sigma[14]),
#  o(nuprime,epsilonbar[6])
# ]
#
#SpherePi(22, 4) := [:
#  o(eta[ 4],mubar[ 5]),
#  o(E(muprime),sigma[15]),
#  o(E(nuprime),epsilonbar[7]),
#  o(nu[4],epsilonbar[7]),
#  o(nu[4],rhosecond),
#  o(nu[4],sigmaprime,nubar[14]),
#  o(nu[4],sigmaprime,epsilon[14])
# ]
#
#SpherePi(23, 5) := [:
#  o(eta[ 5],mubar[ 6]),
#  o(nu[5],epsilonbar[8]),
#  o(zeta[5],sigma[16])
# ]
#
#SpherePi(24, 6) := [:
#  o(eta[ 6],mubar[ 7]),
#  o(zeta[6],sigma[17]),
#  o(WhiteheadP[E(theta)],eta[23])
# ]
#
#SpherePi(25, 7) := [:
#  o(eta[ 7],mubar[ 8]),
#  o(zeta[7],sigma[18])
# ]
#
#SpherePi(26, 8) := [:
#  o(eta[ 8],mubar[ 9]),
#  o(zeta[8],sigma[19]),
#  o(sigma[8],zeta[15])
# ]
#
#SpherePi(27, 9) := [:
#  o(eta[ 9],mubar[10]),
#  o(sigma[9],zeta[16])
# ]
#
#SpherePi(28, 10) := [:
#  o(eta[10],mubar[11]),
#  lambdasecond,
#  xisecond
# ]
#
#SpherePi(29, 11) := [:
#  o(eta[11],mubar[12]),
#  lambdaprime,
#  xiprime
# ]
#
#SpherePi(30, 12) := [:
#  o(eta[12],mubar[13]),
#  E(lambdaprime),
#  E(xiprime),
#  xi[12]
# ]
#
#SpherePi(31, 13) := [:
#  o(eta[13],mubar[14]),
#  xi[13],
#  lambda
# ]
#
#SpherePi(32, 14) := [:
#  o(eta[14],mubar[15]),
#  xi[14],
#  E(lambda)
# ]
#
#SpherePi(33, 15) := [:
#  o(eta[15],mubar[16]),
#  xi[15],
#  E(E(lambda))
# ]
#
#SpherePi(34, 16) := [:
#  o(eta[16],mubar[17]),
#  xi[16],
#  E(E(E(lambda))),
#  nustar[16]
# ]
#
#SpherePi(35, 17) := [:
#  o(eta[17],mubar[18]),
#  xi[17],
#  nustar[17]
# ]
#
#SpherePi(36, 18) := [:
#  o(eta[18],mubar[19]),
#  xi[18] + nustar[18],
#  nustar[18]
# ]
#
#SpherePi(37, 19) := [:
#  o(eta[19],mubar[20]),
#  xi[19] + nustar[19],
#  nustar[19]
# ]
#
#SpherePi(k_, n_) : := [:
#  o(eta[n],mubar[n+1]),
#  nustar[n]
# ] /; k == n+18 && n >= 20
#
#
## 19-stem
#
#
#
#SpherePi(21, 2) := [:
#  o(eta[2],muprime,sigma[14]),
#  o(eta[2],nuprime,epsilonbar[6]),
#  o(eta[2],eta[3],mubar[4])
# ]
#
#SpherePi(22, 3) := [:
#  mubarprime,
#  o(nuprime,mu[6],sigma[15])
# ]
#
#SpherePi(23, 4) := [:
#  E(mubarprime),
#  o(E(nuprime),mu[7],sigma[16]),
#  o(nu[4],mu[7],sigma[16]),
#  o(nu[4],sigmaprime,mu[14]),
#  o(nu[4],E(zetaprime)),
#  o(nu[4],eta[7],epsilonbar[8])
# ]
#
#SpherePi(24, 5) := [:
#  o(nu[5],mu[8],sigma[17]),
#  zetabar[5]
# ]
#
#SpherePi(25, 6) := [:
#  zetabar[6],
#  sigmabar[6]
# ]
#
#SpherePi(26, 7) := [:
#  zetabar[7],
#  sigmabar[7]
# ]
#
#SpherePi(27, 8) := [:
#  zetabar[8],
#  sigmabar[8]
# ]
#
#SpherePi(28, 9) := [:
#  zetabar[9],
#  sigmabar[9]
# ]
#
#SpherePi(29, 10) := [:
#  zetabar[10],
#  sigmabar[10]
# ]
#
#SpherePi(30, 11) := [:
#  zetabar[11],
#  sigmabar[11],
#  o(lambdaprime,eta[29]),
#  o(xiprime,eta[29])
# ]
#
#SpherePi(31, 12) := [:
#  zetabar[12],
#  sigmabar[12],
#  o(E(lambdaprime),eta[30]),
#  o(E(xiprime),eta[30]),
#  omegaprime,
#  o(xi[12],eta[30])
# ]
#
#SpherePi(32, 13) := [:
#  zetabar[13],
#  sigmabar[13],
#  E(omegaprime),
#  o(xi[13],eta[31])
# ]
#
#SpherePi(33, 14) := [:
#  zetabar[14],
#  sigmabar[14],
#  o(omega[14],nu[30])
# ]
#
#SpherePi(34, 15) := [:
#  zetabar[15],
#  sigmabar[15],
#  o(omega[15],nu[31])
# ]
#
#SpherePi(35, 16) := [:
#  zetabar[16],
#  sigmabar[16],
#  o(omega[16],nu[32])
# ]
#
#SpherePi(36, 17) := [:
#  zetabar[17],
#  sigmabar[17],
#  o(omega[17],nu[33])
# ]
#
#SpherePi(37, 18) := [:
#  zetabar[18],
#  sigmabar[18]
# ]
#
#SpherePi(38, 19) := [:
#  zetabar[19],
#  sigmabar[19]
# ]
#
#SpherePi(39, 20) := [:
#  zetabar[20],
#  sigmabar[20],
#  w[20]
# ]
#
#SpherePi(k_, n_) : := [:
#  zetabar[n],
#  sigmabar[n]
# ] /; k == n+19 && n >= 21
#
#


gpad := proc(stem,u)
 local n,J;
 if type(u,list) or type(u,`+`) then
  return(map2(gpad,stem,u));
 elif type(stem,posint) and type(u,indexed) and op(0,u) = x then
  n := op(1,u);
  J := op(2,u);
  if stem > nops(J) then
   J := [op(J),(-1)$(stem-nops(J))];
  fi;
  return(x[n,J]);
 else
  return(u);
 fi;
end:

gunpad := proc(u)
 local n,J;
 if type(u,list) or type(u,`+`) then
  return(map(gunpad,u));
 elif type(u,indexed) and op(0,u) = x then
  n := op(1,u);
  J := op(2,u);
  J := select(p -> p>= 0,J);
  return(x[n,J]);
 else
  return(u);
 fi;
end:

GenealogySort := proc(stem,u)
 gunpad(sort(gpad(stem,u)));
end:

GenealogyName := proc(u)
 if type(u,list) or type(u,`+`) then
  return(map(GenealogyName,u));
 else
  return('GenealogyName'(u));
 fi;
end:

TodaName := proc(u)
 if type(u,list) or type(u,`+`) then
  return(map(TodaName,u));
 else
  return('TodaName'(u));
 fi;
end:

SetGenealogy := proc(a,b)
 GenealogyName(a) := b;
 TodaName(b) := a;
end:

SetStableGenealogy := proc(a,n,J)
 local m,s,i;

 if type(a,symbol) then
  m := 1;
  s := a;
 elif type(a,`*`) and type(op(1,a),integer) and type(op(2,a),symbol) then
  m := op(1,a);
  s := op(2,a);
 else
  return(FAIL);
 fi;

 for i from n to 20 do
  GenealogyName(m*s[i]) := x[i,J];
  TodaName(x[i,J]) := m*s[i];
 od;
end:

for i from 1 to N do 
 for j from 0 to 6 do 
  SetGenealogy(2^j*iota[i],x[i,[0$j]]);
  if i <> 1 and i <> 2 and i <> 4 then 
   SetGenealogy(2^j*w[2*i],x[2*i,[2*i-1,0$(j+1)]]);
  fi;
 od;
od:

for i from 0 to 6 do
 SetGenealogy(2^i*eta[2],x[2,[1,0$i]]);
 SetGenealogy(2^i*nu[4],x[4,[3,0$i]]);
 SetGenealogy(2^i*sigma[8],x[8,[7,0$i]]);
od:

SetStableGenealogy(eta,2,[1]);

for n from 2 to N do
 SetGenealogy(o(eta[n],eta[n+1]),x[n,[1,1]]);
od:

SetGenealogy(o(eta[2],eta[3],eta[4]),x[2,[1,1,1]]):
SetGenealogy(2*nuprime,x[3,[1,1,1]]):
SetGenealogy(nuprime,x[3,[2,1]]):
SetGenealogy(2*E(nuprime),x[4,[1,1,1]]):
SetGenealogy(E(nuprime),x[4,[2,1]]):

SetStableGenealogy(nu,4,[3]):
SetStableGenealogy(2*nu,5,[2,1]):
SetStableGenealogy(4*nu,5,[1,1,1]):

TodaName(x[2,[1,1,1,1]]) := - o(eta[2],nuprime):
GenealogyName(o(eta[2],nuprime)) :=  - x[2,[1,1,1,1]]:

SetGenealogy(2*o(eta[2],nuprime),x[2,[1,2,1]]):

SetGenealogy(o(nuprime,eta[6]),x[3,[2,1,1]]):
SetGenealogy(o(nu[4],eta[7]),x[4,[3,1]]):
SetGenealogy(o(nu[5],eta[8]),x[5,[3,1]]):

(* 5-stem *)

SetGenealogy(o(eta[2],nuprime,eta[6]),x[2,[1,2,1,1]]):
SetGenealogy(o(nuprime,eta[6],eta[7]),x[3,[2,1,1,1]]):
SetGenealogy(o(nu[4], eta[7], eta[8]),x[4, [3, 1, 1]]):
SetGenealogy(o(E(nuprime), eta[7], eta[8]),x[4, [2, 1, 1, 1]]):
SetGenealogy(o(nu[5], eta[8], eta[9]),x[5, [3, 1, 1]]):
SetGenealogy(w[6],x[6,[5,0]]):

(* 6-stem *)

SetGenealogy(o(eta[2], nuprime, eta[6], eta[7]),x[2, [1, 2, 1, 1, 1]]):
SetGenealogy(o(nu[4], nu[7]),x[4, [3, 3]]):
SetGenealogy(2*o(nu[4], nu[7]),x[4, [3, 2, 1]]):
SetGenealogy(4*o(nu[4], nu[7]),x[4, [3, 1, 1, 1]]):

for i from 5 to N do
 SetGenealogy(o(nu[i], nu[i+3]),x[i,[3,3]]);
od:

(* 7-stem *)

SetStableGenealogy(sigma,8,[7]):
SetStableGenealogy(2*sigma,9,[6,1]):
SetStableGenealogy(4*sigma,9,[5,1,1]):
SetStableGenealogy(8*sigma,9,[4,1,1,1]):

SetGenealogy(sigmathird,x[5, [4, 1, 1, 1]]):
SetGenealogy(sigmasecond,x[6, [5, 1, 1]]):
SetGenealogy(2*sigmasecond,x[6, [4, 1, 1, 1]]):
SetGenealogy(sigmaprime,x[7, [6, 1]]):
SetGenealogy(2*sigmaprime,x[7, [5, 1, 1]]):
SetGenealogy(4*sigmaprime,x[7, [4, 1, 1, 1]]):
SetGenealogy(E(sigmaprime),x[8, [6, 1]]):
SetGenealogy(2*E(sigmaprime),x[8, [5, 1, 1]]):
SetGenealogy(4*E(sigmaprime),x[8, [4, 1, 1, 1]]):

(* 8-stem *)

SetStableGenealogy(epsilon,3,[2,3,3]):
SetStableGenealogy(nubar,6, [5, 3]):
SetGenealogy(2*nubar[6],x[6, [5, 2, 1]]):
SetGenealogy(4*nubar[6],x[6, [5, 1, 1, 1]]):
SetGenealogy(o(sigmaprime, eta[14]),x[7, [6, 1, 1]]):
SetGenealogy(o(E(sigmaprime), eta[15]),x[8, [6, 1, 1]]):
SetGenealogy(o(sigma[8], eta[15]),x[8, [7, 1]]):
SetGenealogy(o(sigma[9], eta[16]),x[9, [7, 1]]):

(* 9-stem *)

SetStableGenealogy(mu,3,[2,4,1,1,1]):

for n from 2 to N do 
 SetGenealogy(o(eta[n],epsilon[m+1]),x[n,[1,2,3,3]]):
od:

SetGenealogy(o(nu[4], nu[7], nu[10]),x[4, [3, 3, 3]]):

for n from 4 to N do 
 SetGenealogy(o(nu[n], nu[n+3], nu[n+6]),x[n,[3,3,3]]):
od:

SetGenealogy(o(sigmaprime, eta[14], eta[15]),x[7, [6, 1, 1, 1]]):
SetGenealogy(o(E(sigmaprime), eta[15], eta[16]),x[8, [6, 1, 1, 1]]):
SetGenealogy(o(sigma[8], eta[15], eta[16]),x[8, [7, 1, 1]]):
SetGenealogy(o(sigma[9], eta[16], eta[17]),x[9, [7, 1, 1]]):

(* 10-stem *)

for n from 2 to N do
 SetGenealogy(o(eta[n],mu[n+1]),x[n,[1,2,4,1,1,1]]);
od:

SetGenealogy(o(eta[2], eta[3], epsilon[4]),x[2, [1, 1, 2, 3, 3]]):
SetGenealogy(epsilonprime,x[3, [2, 2, 3, 3]]):
SetGenealogy(2*epsilonprime,x[3, [1, 1, 2, 3, 3]]):
SetGenealogy(E(epsilonprime),x[4, [2, 2, 3, 3]]):
SetGenealogy(2*E(epsilonprime),x[4, [1, 1, 2, 3, 3]]):
SetGenealogy(o(nu[4], sigmaprime),x[4, [3, 6, 1]]):
SetGenealogy(2*o(nu[4], sigmaprime),x[4, [3, 5, 1, 1]]):
SetGenealogy(4*o(nu[4], sigmaprime),x[4, [3, 4, 1, 1, 1]]):
SetGenealogy(o(nu[5], sigma[8]),x[5, [4, 3, 3]]):
SetGenealogy(2*o(nu[5], sigma[8]),x[5, [2, 2, 3, 3]]):
SetGenealogy(4*o(nu[5], sigma[8]),x[5, [1, 1, 2, 3, 3]]):
SetGenealogy(o(nu[6], sigma[9]),x[6, [4, 3, 3]]):
SetGenealogy(2*o(nu[6], sigma[9]),x[6, [2, 2, 3, 3]]):
SetGenealogy(4*o(nu[6], sigma[9]),x[6, [1, 1, 2, 3, 3]]):
SetGenealogy(o(nu[7], sigma[10]),x[7, [4, 3, 3]]):
SetGenealogy(2*o(nu[7], sigma[10]),x[7, [2, 2, 3, 3]]):
SetGenealogy(4*o(nu[7], sigma[10]),x[7, [1, 1, 2, 3, 3]]):
SetGenealogy(o(nu[8], sigma[11]),x[8, [4, 3, 3]]):
SetGenealogy(2*o(nu[8], sigma[11]),x[8, [2, 2, 3, 3]]):
SetGenealogy(4*o(nu[8], sigma[11]),x[8, [1, 1, 2, 3, 3]]):
SetGenealogy(o(sigma[8], nu[15]),x[8, [7, 3]]):
SetGenealogy(2*o(sigma[8], nu[15]),x[8, [7, 2, 1]]):
SetGenealogy(4*o(sigma[8], nu[15]),x[8, [7, 1, 1, 1]]):
SetGenealogy(o(sigma[9], nu[16]),x[9, [7, 3]]):
SetGenealogy(2*o(sigma[9], nu[16]),x[9, [7, 2, 1]]):
SetGenealogy(4*o(sigma[9], nu[16]),x[9, [7, 1, 1, 1]]):
SetGenealogy(o(sigma[10], nu[17]),x[10, [7, 3]]):
SetGenealogy(2*o(sigma[10], nu[17]),x[10, [7, 2, 1]]):
SetGenealogy(o(sigma[11], nu[18]),x[11, [7, 3]]):

(* 11-stem *)

GenealogyName(o(eta[2], epsilonprime)) :=
 x[2, [1, 2, 2, 3, 3]] + x[2, [1, 1, 1, 2, 3, 3]];
TodaName(x[2,[1,2,2,3,3]]) := 3*o(eta[2],epsilonprime):

SetGenealogy(2*o(eta[2], epsilonprime),x[2, [1, 1, 1, 2, 3, 3]]):
SetGenealogy(o(eta[2], eta[3], mu[4]),x[2, [1, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(muprime,x[3, [2, 2, 4, 1, 1, 1]]):
SetGenealogy(2*muprime,x[3, [1, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(epsilon[3], nu[11]),x[3, [2, 3, 3, 3]]):
SetGenealogy(o(nuprime, epsilon[6]),x[3, [2, 1, 2, 3, 3]]):
SetGenealogy(E(muprime),x[4, [2, 2, 4, 1, 1, 1]]):
SetGenealogy(2*E(muprime),x[4, [1, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(epsilon[4], nu[12]),x[4, [2, 3, 3, 3]]):
SetGenealogy(o(E(nuprime), epsilon[7]),x[4, [2, 1, 2, 3, 3]]):
SetGenealogy(o(nu[4], sigmaprime, eta[14]),x[4, [3, 6, 1, 1]]):
SetGenealogy(o(nu[4], nubar[7]),x[4, [3, 5, 3]]):
SetGenealogy(o(nu[4], epsilon[7]),x[4, [3, 2, 3, 3]]):
SetGenealogy(o(nu[5], nubar[8]),x[5, [3, 5, 3]]):
SetGenealogy(o(nu[5], epsilon[8]),x[5, [3, 2, 3, 3]]):
SetGenealogy(o(nubar[6], nu[14]),x[6, [5, 3, 3]]):
SetGenealogy(2*o(nubar[6], nu[14]),x[6, [3, 2, 3, 3]]):
SetGenealogy(o(nubar[7], nu[15]),x[7, [5, 3, 3]]):
SetGenealogy(o(nubar[8], nu[16]),x[8, [5, 3, 3]]):
SetGenealogy(o(nubar[9], nu[17]),x[9, [5, 3, 3]]):

SetStableGenealogy(zeta,5,[4, 4, 1, 1, 1]):
SetStableGenealogy(2*zeta,5, [2, 2, 4, 1, 1, 1]):
SetStableGenealogy(4*zeta,5, [1, 1, 2, 4, 1, 1, 1]):

(* 12-stem *)

GenealogyName(o(eta[2],muprime)) := 
 x[2, [1, 2, 2, 4, 1, 1, 1]] + x[2, [1, 1, 1, 2, 4, 1, 1, 1]]:

TodaName(x[2,[1,2,2,4,1,1,1]]) := 3*o(eta[2],muprime):

SetGenealogy(2*o(eta[2],muprime),x[2,[1,1,1,2,4,1,1,1]]):
SetGenealogy(o(eta[2],epsilon[3],nu[11]),x[2,[1,2,3,3,3]]):
SetGenealogy(o(eta[2],nuprime,epsilon[6]),x[2,[1,2,1,2,3,3]]):
SetGenealogy(o(nuprime,mu[6]),x[3,[2,1,2,4,1,1,1]]):
SetGenealogy(o(nuprime,eta[6],epsilon[7]),x[3,[2,1,1,2,3,3]]):
SetGenealogy(o(nu[4],sigmaprime,eta[14],eta[15]),x[4,[3,6,1,1,1]]):
SetGenealogy(o(nu[4],nu[7],nu[10],nu[13]),x[4,[3,3,3,3]]):
SetGenealogy(o(nu[4],mu[7]),x[4,[3,2,4,1,1,1]]):
SetGenealogy(o(nu[4],eta[7],epsilon[8]),x[4,[3,1,2,3,3]]):
SetGenealogy(o(E(nuprime),mu[7]),x[4,[2,1,2,4,1,1,1]]):
SetGenealogy(o(E(nuprime),eta[7],epsilon[8]),x[4,[2,1,1,2,3,3]]):
SetGenealogy(o(nu[5],nu[8],nu[11],nu[14]),x[5,[3,3,3,3]]):
SetGenealogy(o(nu[5],mu[8]),x[5,[3,2,4,1,1,1]]):
SetGenealogy(o(nu[5],eta[8],epsilon[9]),x[5,[3,1,2,3,3]]):
SetGenealogy(o(w[6],sigma[11]),x[6,[5,6,1]]):
SetGenealogy(2*o(w[6],sigma[11]),x[6,[5,5,1,1]]):
SetGenealogy(4*o(w[6],sigma[11]),x[6,[5,4,1,1,1]]):
SetGenealogy(8*o(w[6],sigma[11]),x[6,[3,2,4,1,1,1]]):
SetGenealogy(8*o(w[6], sigma[11]),x[6,[3,2,4,1,1,1]]):
SetGenealogy(o(w[10], nu[19]),x[10, [9, 2, 1]]):
SetGenealogy(2*o(w[10], nu[19]),x[10, [9, 1, 1, 1]]):
SetGenealogy(thetaprime,x[11, [10, 1, 1]]):
SetGenealogy(theta,x[12, [11, 1]]):
SetGenealogy(E(thetaprime),x[12, [10, 1, 1]]):
SetGenealogy(E(theta),x[13, [11, 1]]):

(* 13-stem *)
SetGenealogy(o(eta[2], nuprime, mu[6]),x[2, [1, 2, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(eta[2], nuprime, eta[6], epsilon[7]),x[2, [1, 2, 1, 1, 2, 3, 3]]):
SetGenealogy(o(nuprime, eta[6], mu[7]),x[3, [2, 1, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(nu[4], nu[7], sigma[10]),x[4, [3, 4, 3, 3]]):
SetGenealogy(2*o(nu[4], nu[7], sigma[10]),x[4, [3, 2, 2, 3, 3]]):
SetGenealogy(4*o(nu[4], nu[7], sigma[10]),x[4, [3, 1, 1, 2, 3, 3]]):
SetGenealogy(o(nu[4], eta[7], mu[8]),x[4, [3, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(E(nuprime), eta[7], mu[8]),x[4, [2, 1, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(nu[5], sigma[8], nu[15]),x[5, [4, 3, 3, 3]]):
SetGenealogy(o(nu[5], eta[8], mu[9]),x[5, [3, 1, 2, 4, 1, 1, 1]]):
SetGenealogy(o(nu[6], sigma[9], nu[16]),x[6, [4, 3, 3, 3]]):
SetGenealogy(o(nu[7], sigma[10], nu[17]),x[7, [4, 3, 3, 3]]):
SetGenealogy(o(sigma[8], nu[15], nu[18]),x[8, [7, 3, 3]]):
SetGenealogy(o(nu[8], sigma[11], nu[18]),x[8, [4, 3, 3, 3]]):
SetGenealogy(o(sigma[9], nu[16], nu[19]),x[9, [7, 3, 3]]):
SetGenealogy(o(sigma[10], nu[17], nu[20]),x[10, [7, 3, 3]]):
SetGenealogy(o(sigma[11], nu[18], nu[21]),x[11, [7, 3, 3]]):
SetGenealogy(o(thetaprime, eta[23]),x[11, [10, 1, 1, 1]]):
SetGenealogy(o(theta, eta[24]),x[12, [11, 1, 1]]):
SetGenealogy(o(E(thetaprime), eta[24]),x[12, [10, 1, 1, 1]]):
SetGenealogy(o(E(theta), eta[25]),x[13, [11, 1, 1]]):

