# This file sets up the letters of the alphabet as one-dimensional simplicial
# complexes.  

letters := table():

alphabet_list := [["A","B","C","D","E"],
                  ["F","G","H","I","J"],
                  ["K","L","M","N","O"],
                  ["P","Q","R","S","T"],
                  ["U","V","W","X","Y"]]:

alphabet_type_list := [
 ["C","G","L","M","N","S","U","V","W"],
 ["E","F","J","T","Y"],
 ["H","I"],
 ["K","X"],
 ["O","D","A","Q"],
 ["B"]
]:
 
set_map := proc(T)
 local P,e,s,t;
 T["map"] := table():
 P := T["embedding"]:
 for e in T["max_simplices"] do 
  T["map"][e] := unapply((1-t) *~ P[e[1]] +~ t *~ P[e[2]],t);
 od:
end:

set_alt_map := proc(T)
 local P,e,s,t;
 T["alt_map"] := table():
 P := T["alt_embedding"]:
 for e in T["max_simplices"] do 
  T["alt_map"][e] := unapply((1-t) *~ P[e[1]] +~ t *~ P[e[2]],t);
 od:
end:

set_isotopy := proc(T)
 local P,Q,e,s,t;
 T["isotopy"] := table():
 for e in T["max_simplices"] do 
  T["isotopy"][e] := 
   unapply((1-s) *~ T["map"][e](t) +~ s *~ T["alt_map"][e](t),s,t);
 od:
end:

rotate_isotopy := proc(T,a)
 local P0,P1,P2,e,v,s,t;
 P0 := eval(T["alt_embedding"]):
 P1 := eval(T["alt_map"]):
 P2 := eval(T["isotopy"]):
 T["alt_embedding"] := table():
 T["alt_map"] := table():
 T["isotopy"] := table():
 for v in T["vertices"] do
  T["alt_embedding"][v] := rot(a,P0[v]):
 od:
 for e in T["max_simplices"] do 
  T["alt_map"][e] := unapply(rot(a,P1[e](t)),t):
  T["isotopy"][e] := unapply(rot(a*s,P2[e](s,t)),s,t):
 od:
end:

translate_letter := proc(T,a)
 local P0,P1,P2,P3,P4,e,v,s,t;
 P0 := eval(T["embedding"]):
 P1 := eval(T["map"]):
 P2 := eval(T["alt_embedding"]):
 P3 := eval(T["alt_map"]):
 P4 := eval(T["isotopy"]):
 T["embedding"] := table():
 T["map"] := table():
 T["alt_embedding"] := table():
 T["alt_map"] := table():
 T["isotopy"] := table():
 for v in T["vertices"] do
  T["embedding"][v] := P0[v] +~ a:
  T["alt_embedding"][v] := P3[v] +~ a:
 od:
 for e in T["max_simplices"] do 
  T["map"][e] := unapply(P1[e](t) +~ a,t):
  T["alt_map"][e] := unapply(P3[e](t) +~ a,t):
  T["isotopy"][e] := unapply(P2[e](s,t) +~ a,s,t):
 od:
end:

pol := (r,t) -> evalf([r * cos(Pi*t),r * sin(Pi*t)]):
rot := (t,x) -> evalf([cos(Pi*t)*x[1]-sin(Pi*t)*x[2],sin(Pi*t)*x[1] + cos(Pi*t)*x[2]]):

show_map := (T,s) -> 
 display(seq(plot([op(T["map"][e](t)),t=0..1]),e in T["max_simplices"]),axes=none,scaling=constrained):

show_alt_map := (T,s) -> 
 display(seq(plot([op(T["alt_map"][e](t)),t=0..1]),e in T["max_simplices"]),axes=none,scaling=constrained):

show_isotopy := (T,s) -> 
 display(seq(plot([op(T["isotopy"][e](s,t)),t=0..1]),e in T["max_simplices"]),axes=none,scaling=constrained):

show_movie := (T) -> 
 display([seq(show_isotopy(T,s),s=0..1,0.02)],insequence=true,view=[-1.5..1.5,-1.5..1.5]):

show_list_map := proc(L)
 display(seq(seq(
   translate(show_map(letters[L[i][j]]),2*j,-3*i),
  j=1..nops(L[i])),i=1..nops(L)),scaling=constrained);
end:

show_list_alt_map := proc(L)
 display(seq(seq(
   translate(show_alt_map(letters[L[i][j]]),3*j,-3*i),
  j=1..nops(L[i])),i=1..nops(L)),scaling=constrained);
end:

show_list_isotopy := proc(L,s)
 display(seq(seq(
   translate(show_isotopy(letters[L[i][j]],s),3*j,-3*i),
  j=1..nops(L[i])),i=1..nops(L)),scaling=constrained);
end:

show_list_movie := proc(L)
 display([seq(show_list_isotopy(L,s),s=0..1,0.02)],insequence=true):
end:

tikz_map := proc(T)
 local s,e,u,n;
 s := "";
 for e in T["max_simplices"] do
  u := T["map"][e];
  if type(u(t),list(polynom(realcons,t))) and
     max(map(degree,u,t)) <= 1 then
   n := 1;
  else
   n := 16;
  fi;
  s := cat(s," \\draw ",
    StringTools[Join]([seq(sprintf("(%.3f,%.3f)",op(u(i/n))),i=0..n)]," -- "),
    ";\n");
 od:
 return s;
end:

tikz_alt_map := proc(T)
 local s,e,u,n;
 s := "";
 for e in T["max_simplices"] do
  u := T["alt_map"][e];
  if type(u(t),list(polynom(realcons,t))) and
     max(map(degree,u,t)) <= 1 then
   n := 1;
  else
   n := 16;
  fi;
  s := cat(s," \\draw ",
    StringTools[Join]([seq(sprintf("(%.3f,%.3f)",op(u(i/n))),i=0..n)]," -- "),
    ";\n");
 od:
 return s;
end:

tikz_list_map := proc(L,{width::numeric := 2},{height::numeric := 3})
 cat(seq(seq(
  cat(
   sprintf("\\begin{scope}[shift={(%f,%f)}]\n",width*j,-height*i),
   tikz_map(letters[L[i][j]]),
   "\\end{scope}\n"),
   j=1..nops(L[i])),i=1..nops(L)));
end:

tikz_list_alt_map := proc(L,{width::numeric := 3.2},{height::numeric := 3})
 cat(seq(seq(
  cat(
   sprintf("\\begin{scope}[shift={(%f,%f)}]\n",width*j,-height*i),
   tikz_alt_map(letters[L[i][j]]),
   "\\end{scope}\n"),
   j=1..nops(L[i])),i=1..nops(L)));
end:

######################################################################
# A

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[4,5],[2,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([
 1 = [-1,-1], 2 = [-0.5,0], 3 = [0,1], 4 = [0.5,0], 5 = [1,-1]
]):
T["alt_embedding"] := table([
 1 = [-1.5,0], 2 = [-1,0], 3 = [0,1], 4 = [1,0], 5 = [1.5,0]
]):
set_map(T): 
set_alt_map(T):
T["alt_map"][[2,3]] := (t) -> [-cos(Pi/2*t),sin(Pi/2*t)]:
T["alt_map"][[3,4]] := (t) -> [ sin(Pi/2*t),cos(Pi/2*t)]:
T["alt_map"][[2,4]] := (t) -> [-cos(Pi*t),-sin(Pi*t)]:
set_isotopy(T):
letters["A"] := eval(T):

######################################################################
# B

T := table():
T["vertices"] := [1,2,3,4,5,6]:
T["max_simplices"] := [[1,2],[1,4],[2,3],[2,5],[3,6],[4,5],[5,6]]:
T["embedding_dim"] := 2:
T["embedding"] := table([
 1 = [-0.5,-1],2=[-0.5,0],3=[-0.5,1],4=[0,-1],5=[0,0],6=[0,1]
]):
T["alt_embedding"] := table([
 1 = pol(1,-2/3), 2 = pol(1,1), 3 = pol(1,2/3), 4 = pol(1,-1/3), 5 = pol(1,0), 6 = pol(1,1/3)
]):
set_map(T): 
set_alt_map(T):
T["map"][[4,5]] := (t) -> [0,-0.5] +~ pol(0.5,t-0.5):
T["map"][[5,6]] := (t) -> [0, 0.5] +~ pol(0.5,t-0.5):
T["alt_map"][[1,2]] := (t) -> pol(1,(-2-t)/3):
T["alt_map"][[1,4]] := (t) -> pol(1,(-2+t)/3):
T["alt_map"][[2,3]] := (t) -> pol(1,(-3-t)/3):
T["alt_map"][[3,6]] := (t) -> pol(1,( 2-t)/3):
T["alt_map"][[4,5]] := (t) -> pol(1,(-1+t)/3):
T["alt_map"][[5,6]] := (t) -> pol(1,(   t)/3):
set_isotopy(T):
letters["B"] := eval(T):

######################################################################
# C

T := table():
T["vertices"] := [1,2]:
T["max_simplices"] := [[1,2]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1 = pol(1,0.4) *~ [0.8,1], 2 = pol(1,-0.4) *~ [0.8,1]]):
T["alt_embedding"] := table([1 = [0,1], 2=[0,-1]]):
T["map"] := table([[1,2] = ((t) -> pol(1,0.4 + 1.2*t) *~ [0.8,1])]):
set_alt_map(T):
set_isotopy(T):
letters["C"] := eval(T):

######################################################################
# D

T := table():
T["vertices"] := [1,2,3]:
T["max_simplices"] := [[1,2],[1,3],[2,3]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1 = [-0.5,-1], 2=[-0.5,1], 3 = [0.5,0]]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,1], 3 = [1,0]]):
set_map(T):
T["map"][[1,3]] := (t) -> [-0.5,0] +~ pol(1,-0.5 + 0.5*t):
T["map"][[2,3]] := (t) -> [-0.5,0] +~ pol(1, 0.5 - 0.5*t):
T["alt_map"] := table():
T["alt_map"][[1,2]] := (t) -> pol(1,-0.5 - t):
T["alt_map"][[1,3]] := (t) -> pol(1,-0.5 + 0.5*t):
T["alt_map"][[2,3]] := (t) -> pol(1, 0.5 - 0.5*t):
set_isotopy(T):
letters["D"] := eval(T):

######################################################################
# E

T := table():
T["vertices"] := [1,2,3,4,5,6]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[4,5],[3,6]]:
T["embedding_dim"] := 2:
T["embedding"] := table([
 1 = [0.5,-1], 2 = [-0.5,-1], 3 = [-0.5,0], 4 = [-0.5,1], 5 = [0.5,1], 6 = [0,0]
]):
T["alt_embedding"] := table([
 1 = [-1,-1], 2 = [-1,-0.5], 3 = [-1,0], 4 = [-1,0.5], 5 = [-1,1], 6 = [1,0]
]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
T["isotopy"][[1,2]] := (s,t) -> (1-s) *~ [-0.5,-1] +~ s *~ [-1,-0.5] +~ pol((1-0.5*s)*(1-t),-s/2):
T["isotopy"][[4,5]] := (s,t) -> (1-s) *~ [-0.5, 1] +~ s *~ [-1, 0.5] +~ pol((1-0.5*s)*(1-t), s/2):
rotate_isotopy(T,-0.5):
letters["E"] := eval(T):

######################################################################
# F

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[2,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([
 1 = [-0.5,-1], 2 = [-0.5,0], 3 = [-0.5,1], 4 = [0.5,1], 5 = [0,0]
]):
T["alt_embedding"] := table([
 1 = [-1,-1], 2 = [-1,0], 3 = [-1,0.5], 4 = [-1,1], 5 = [1,0]
]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
T["isotopy"][[3,4]] := (s,t) -> (1-s) *~ [-0.5, 1] +~ s *~ [-1, 0.5] +~ pol((1-0.5*s)*(1-t), s/2):
rotate_isotopy(T,-0.5):
letters["F"] := eval(T):

######################################################################
# G

T := table():
T["vertices"] := [1,2,3]:
T["max_simplices"] := [[1,2],[2,3]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1 = pol(1,0.4) *~ [0.8,1], 2 = pol(1,-0.4) *~ [0.8,1],
                         3 = pol(1,-0.4) *~ [0.8,1] +~ [0,-0.4]
                         ]):
T["alt_embedding"] := table([1 = [0,1], 2=[0,0], 3=[0,-1]]):
set_map(T):
T["map"][[1,2]] := ((t) -> pol(1,0.4 + 1.2*t) *~ [0.8,1]):
set_alt_map(T):
set_isotopy(T):
letters["G"] := eval(T):

######################################################################
# H

T := table():
T["vertices"] := [1,2,3,4,5,6]:
T["max_simplices"] := [[1,2],[2,3],[2,5],[4,5],[5,6]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.5,-1],2=[-0.5,0],3=[-0.5,1],
                         4=[ 0.5,-1],5=[ 0.5,0],6=[ 0.5,1]
                         ]):
T["alt_embedding"] := table([1 = [-1,-1], 2=[-1,0], 3=[-1,1],
                             4=[1,-1],5=[1,0],6=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["H"] := eval(T):

######################################################################
# I

T := table():
T["vertices"] := [1,2,3,4,5,6]:
T["max_simplices"] := [[1,2],[2,3],[2,5],[4,5],[5,6]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.2,-1],2=[0,-1],3=[0.2,-1],
                         4=[-0.2,1],5=[0,1],6=[0.2,1]
                         ]):
T["alt_embedding"] := table([1 = [-1,-1], 2=[0,-1], 3=[1,-1],
                             4=[-1,1],5=[0,1],6=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["I"] := eval(T):

######################################################################
# J

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,4],[3,4],[4,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.6,-0.7],2=[0,-0.7],3=[-0.5,1],
                         4=[0,1],5=[0.5,1]
                         ]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,0], 3=[-1,1],
                             4=[0,1],5=[1,1]]):
set_map(T):
T["map"][[1,2]] := (t) -> [-0.3,-0.7] +~ pol(0.3,-1+t):
set_alt_map(T):
set_isotopy(T):
letters["J"] := eval(T):

######################################################################
# K

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[2,4],[2,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.5,-1],2=[-0.5,0],3=[-0.5,1],
                         4=[0.5,-1],5=[0.5,1]
                         ]):
T["alt_embedding"] := table([1 = [-1,-1], 2=[0,0], 3=[-1,1],
                             4=[1,-1],5=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["K"] := eval(T):

######################################################################
# L

T := table():
T["vertices"] := [1,2,3]:
T["max_simplices"] := [[1,2],[2,3]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[0.5,-1],2=[-0.5,-1],3=[-0.5,1]]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,0], 3=[0,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["L"] := eval(T):

######################################################################
# M

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[4,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.6,-1],2=[-0.3,1],3=[0,-1],4=[0.3,1],5=[0.6,-1]]):
T["alt_embedding"] := table([1 = [-1,0], 2=[-0.5,0], 3=[0,0],4=[0.4,0],5=[1,0]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["M"] := eval(T):

######################################################################
# N

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[3,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.5,-1],2=[-0.5,1],3=[0.5,-1],4=[0.5,1]]):
T["alt_embedding"] := table([1 = [-1,0], 2=[-0.33,0], 3=[0.33,0],4=[1,0]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["N"] := eval(T):

######################################################################
# O

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[1,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=pol(1,0) *~ [0.6,1], 2=pol(1,0.5) *~ [0.6,1],
                         3=pol(1,1) *~ [0.6,1], 4=pol(1,1.5) *~ [0.6,1]]):
T["alt_embedding"] := table([1 = pol(1,0),2=pol(1,0.5),3=pol(1,1),4=pol(1,1.5)]):
set_map(T):
set_alt_map(T):
T["map"][[1,2]] := (t) -> pol(1,0.5* t   ) *~ [0.6,1]:
T["map"][[2,3]] := (t) -> pol(1,0.5*(t+1)) *~ [0.6,1]:
T["map"][[3,4]] := (t) -> pol(1,0.5*(t+2)) *~ [0.6,1]:
T["map"][[1,4]] := (t) -> pol(1,0.5*(4-t)) *~ [0.6,1]:
T["alt_map"][[1,2]] := (t) -> pol(1,0.5* t   ):
T["alt_map"][[2,3]] := (t) -> pol(1,0.5*(t+1)):
T["alt_map"][[3,4]] := (t) -> pol(1,0.5*(t+2)):
T["alt_map"][[1,4]] := (t) -> pol(1,0.5*(4-t)):
set_isotopy(T):
letters["O"] := eval(T):

######################################################################
# P

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[2,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.25,-1],2=[-0.25,0],3=[-0.25,1],4=[0.5,0.5]]):
T["alt_embedding"] := table([1=[0,-1.5],2=[0,-1],3=pol(1,2/3),4=pol(1,1/3)]):
set_map(T):
set_alt_map(T):
T["map"][[2,4]] := (t) -> pol(0.5,0.5*(t-1)) *~ [1.5,1] +~ [-0.25,0.5]:
T["map"][[3,4]] := (t) -> pol(0.5,0.5*(1-t)) *~ [1.5,1] +~ [-0.25,0.5]:
T["alt_map"][[2,3]] := (t) -> pol(1,-1/2-2/3*t):
T["alt_map"][[2,4]] := (t) -> pol(1,-1/2+2/3*t):
T["alt_map"][[3,4]] := (t) -> pol(1,5/6-2/3*t):
set_isotopy(T):
rotate_isotopy(T,0.5):
letters["P"] := eval(T):

######################################################################
# Q

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[1,3],[1,4],[1,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([
 1= pol(1,-1/4)   *~ [0.6,1],
 2= pol(1,5/12)   *~ [0.6,1],
 3= pol(1,13/12)  *~ [0.6,1],
 4= pol(1.3,-1/4) *~ [0.6,1],
 5= pol(0.7,-1/4) *~ [0.6,1]
]):
T["alt_embedding"] := 
table([
 1= pol(1,-1/4),
 2= pol(1,5/12),
 3= pol(1,13/12),
 4= pol(1.5,-1/4),
 5= pol(0.5,-1/4)
]):
set_map(T):
set_alt_map(T):
T["map"][[1,2]] := (t) -> pol(1,-1/4+2/3*t) *~ [0.6,1]:
T["map"][[1,3]] := (t) -> pol(1,-1/4-2/3*t) *~ [0.6,1]:
T["map"][[2,3]] := (t) -> pol(1,5/12+2/3*t) *~ [0.6,1]:
T["alt_map"][[1,2]] := (t) -> pol(1,-1/4+2/3*t):
T["alt_map"][[1,3]] := (t) -> pol(1,-1/4-2/3*t):
T["alt_map"][[2,3]] := (t) -> pol(1,5/12+2/3*t):
set_isotopy(T):
rotate_isotopy(T,0.25):
letters["Q"] := eval(T):

######################################################################
# R

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[2,4],[2,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.25,-1],2=[-0.25,0],3=[-0.25,1],4=[0.5,0.5],5=[0.5,-1]]):
T["alt_embedding"] := table([1=[-0.5,-1.5],2=[0,-1],3=pol(1,2/3),4=pol(1,1/3),5=[0.5,-1.5]]):
set_map(T):
set_alt_map(T):
T["map"][[2,4]] := (t) -> pol(0.5,0.5*(t-1)) *~ [1.5,1] +~ [-0.25,0.5]:
T["map"][[3,4]] := (t) -> pol(0.5,0.5*(1-t)) *~ [1.5,1] +~ [-0.25,0.5]:
T["alt_map"][[2,3]] := (t) -> pol(1,-1/2-2/3*t):
T["alt_map"][[2,4]] := (t) -> pol(1,-1/2+2/3*t):
T["alt_map"][[3,4]] := (t) -> pol(1,5/6-2/3*t):
set_isotopy(T):
rotate_isotopy(T,0.5):
letters["R"] := eval(T):

######################################################################
# S

T := table():
T["vertices"] := [1,2,3]:
T["max_simplices"] := [[1,2],[2,3]]:
T["embedding_dim"] := 2:
theta := -0.05;
T["embedding"] := table([
 1=rot(theta,[0,-0.5] +~ pol(0.5,-0.7)),
 2=rot(theta,[0,0],3=[0,0.5] +~ pol(0.5,0.3))
 ]):
T["alt_embedding"] := table([1=[0,-1],2=[0,0],3=[0,1]]):
set_map(T):
set_alt_map(T):
T["map"][[1,2]] := (t) -> rot(theta,[0,-0.5] +~ pol(0.5,-0.7+1.2*t)):
T["map"][[2,3]] := (t) -> rot(theta,[0, 0.5] +~ pol(0.5,-0.5-1.2*t)):
set_isotopy(T):
letters["S"] := eval(T):

######################################################################
# T

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[2,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[0,-1],2=[0,1],3=[-0.7,1],4=[0.7,1]]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,1], 3=[-1,1],4=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["T"] := eval(T):

######################################################################
# U

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[3,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.6,1],2=[-0.6,-0.4],3=[0.6,-0.4],4=[0.6,1]]):
T["alt_embedding"] := table([1 = [-1,0], 2=[-0.33,0], 3=[0.33,0],4=[1,0]]):
set_map(T):
set_alt_map(T):
T["map"][[2,3]] := (t) -> [0,-0.4] +~ pol(0.6,t-1):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["U"] := eval(T):

######################################################################
# V

T := table():
T["vertices"] := [1,2,3]:
T["max_simplices"] := [[1,2],[2,3]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.6,1],2=[0,-1],3=[0.6,1]]):
T["alt_embedding"] := table([1 = [-1,0], 2=[0,0], 3=[1,0]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["V"] := eval(T):

######################################################################
# W

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[3,4],[4,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.6,1],2=[-0.3,-1],3=[0,1],4=[0.3,-1],5=[0.6,1]]):
T["alt_embedding"] := table([1 = [-1,0], 2=[-0.5,0], 3=[0,0],4=[0.4,0],5=[1,0]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
rotate_isotopy(T,-0.5):
letters["W"] := eval(T):

######################################################################
# X

T := table():
T["vertices"] := [1,2,3,4,5]:
T["max_simplices"] := [[1,2],[2,3],[2,4],[2,5]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[-0.5,-1],2=[0,0],3=[-0.5,1],
                         4=[0.5,-1],5=[0.5,1]
                         ]):
T["alt_embedding"] := table([1 = [-1,-1], 2=[0,0], 3=[-1,1],
                             4=[1,-1],5=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["X"] := eval(T):

######################################################################
# Y

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[2,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[0,-1],2=[0,0],3=[-0.7,1],4=[0.7,1]]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,1], 3=[-1,1],4=[1,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["Y"] := eval(T):

######################################################################
# Z

T := table():
T["vertices"] := [1,2,3,4]:
T["max_simplices"] := [[1,2],[2,3],[3,4]]:
T["embedding_dim"] := 2:
T["embedding"] := table([1=[0.5,-1],2=[-0.5,-1],3=[0.5,1],4=[-0.5,1]]):
T["alt_embedding"] := table([1 = [0,-1], 2=[0,-0.33], 3=[0,0.33],4=[0,1]]):
set_map(T):
set_alt_map(T):
set_isotopy(T):
letters["Z"] := eval(T):
