# The function brent_fsolve uses Brent's algorithm to find a root of
# a real valued function of one variable.   This code is based on the
# Matlab implementation by John Burkardt, which is in turn based on the 
# original Fortran implementation by Richard Brent.  However, this
# version is designed for the case where we want to retain a lot
# of additional information that is generated in the process of 
# evaluating the relevant function.
#
# The first argument F should be a function which accepts a single
# real argument t and returns a table F(t).  This should contain an 
# entry F(t)["err"], which we want to be zero.  The second and third
# arguments should be numbers a and b such that F(a)["err"] and 
# F(b)["err"] have opposite signs.  Other entries in F(t) can contain
# auxiliary information generated during the calculation.
#
# If F(a) and/or F(b) have already been computed, then they can be 
# supplied as the arguments Fa_ and Fb_.  Otherwise, these arguments
# should be set to false.

#@ brent_fsolve 
brent_fsolve := proc(F,a,b,Fa_,Fb_,tol_,epsilon_) 
 local tol,tol1,epsilon,c,sa,sb,sc,Fa,Fb,Fc,fa,fb,fc,d,e,m,p,q,r,s,steps,ret;

 tol := `if`(nargs > 5,tol_,10.^(-20));
 epsilon := `if`(nargs > 6,epsilon_,10.^(2 - Digits));

 sa := a;
 sb := b;
 if nargs < 4 or Fa_ = false then Fa := eval(F(sa)); else Fa := eval(Fa_); fi;
 if nargs < 5 or Fb_ = false then Fb := eval(F(sb)); else Fb := eval(Fb_); fi;
 fa := Fa["err"];
 fb := Fb["err"];

 if not((fa <= 0 and 0 <= fb) or 
        (fb <= 0 and 0 <= fa)) then
  error("function has the same sign at endpoints");
 fi;

 c := sa;
 fc := fa;
 Fc := eval(Fa);
 e := sb - sa;
 d := e;

 steps := 0;
 
 while true do
  steps := steps+1;
  
  if ( abs ( fc ) < abs ( fb ) ) then
   sa := sb;
   sb := c;
   c := sa;
   fa := fb;
   fb := fc;
   fc := fa;
   Fa := eval(Fb);
   Fb := eval(Fc);
   Fc := eval(Fa);
  fi;

  tol1 := 2.0 * epsilon * abs ( sb ) + tol;
  m := 0.5 * ( c - sb );

  if ( abs ( m ) <= tol or fb = 0.0 ) then
   break;
  fi;

  if ( abs ( e ) < tol or abs ( fa ) <= abs ( fb ) ) then
   e := m;
   d := e;
  else
   s := fb / fa;
   if ( sa = c ) then
    p := 2.0 * m * s;
    q := 1.0 - s;
   else
    q := fa / fc;
    r := fb / fc;
    p := s * ( 2.0 * m * q * ( q - r ) - ( sb - sa ) * ( r - 1.0 ) );
    q := ( q - 1.0 ) * ( r - 1.0 ) * ( s - 1.0 );
   fi;

   if ( 0.0 < p ) then
    q := - q;
   else
    p := - p;
   fi;

   s := e;
   e := d;

   if ( 2.0 * p < 3.0 * m * q - abs ( tol * q ) and p < abs ( 0.5 * s * q ) ) then
    d := p / q;
   else
    e := m;
    d := e;
   fi;
  fi;

  sa := sb;
  fa := fb;
  Fa := eval(Fb);

  if ( tol < abs ( d ) ) then
   sb := sb + d;
  elif ( 0.0 < m ) then
   sb := sb + tol;
  else
   sb := sb - tol;
  fi;

  Fb := eval(F(sb));
  fb := Fb["err"];

  if ( ( 0.0 < fb and 0.0 < fc ) or ( fb <= 0.0 and fc <= 0.0 ) ) then
   c := sa;
   fc := fa;
   Fc := eval(Fa);
   e := sb - sa;
   d := e;
  fi;
 od;

 ret := eval(Fb);
 ret["steps"] := steps;
 
 return [sb,eval(ret)];
end:


