#@ Not autoload

# 3-stem
SpherePi(5,2) := [[2,o(eta[2],eta[3],eta[4])]]:

# NB nuprime is usually only defined at p=2. 
# Presumably we get a generator from the unstable J-map?
SpherePi(6,3) := [[12,nuprime]]: 

SpherePi(7,4) := [[infinity,nu[4]],[12,E(nuprime)]]:

for i from 5 to 20 do 
 SpherePi(i+3,i) := [[24,nu[i]]]:
od:

# 4-stem
SpherePi(6,2) := [[12,o(eta[2],nuprime)]]:
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
SpherePi(10, 4) := [[24,o(nu[4],nu[7])],3]:

for i from 5 to 20 do
 SpherePi(i+6,i) := [[2,o(nu[i],nu[i+3])]]:
od:

# 7-stem

SpherePi( 9, 2) := [3]:
SpherePi(10, 3) := [15]:
SpherePi(11, 4) := [15]:
SpherePi(12, 5) := [30]:
SpherePi(13, 6) := [60]:
SpherePi(14, 7) := [120]:
SpherePi(15, 8) := [[infinity,sigma[8]],120]:

for i from 9 to 20 do
 SpherePi(i+7,i) := [[240,sigma[i]]]:
od:

# 8-stem

SpherePi(10, 2) := [15]:
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
