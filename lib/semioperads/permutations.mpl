`gamma/permutations` := (J) -> proc(s,t)
 local k,i,m,tt;
 k := nops(J);
 i := `+`(op(J));
 tt := [];
 m := 0;
 for i from 1 to k do
  tt := [op(tt),t[i] +~ m];
  m := m + J[i];
 od:
 return [seq(op(tt[s[i]]),i=1..k)];
end:

`eta/permutations` := [1];

`circ/permutations` := (i,m,n) -> proc(s,t)
 local u,p;
 u := NULL;
 for p from 1 to m do
  if s[p] < i then
   u := u,s[p]
  elif s[p] = i then
   u := u , op(t +~ (i - 1));
  else
   u := u,s[p]+n-1;
  fi;
 od;
 return [u];
end:

