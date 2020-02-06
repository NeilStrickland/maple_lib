klein_embedding := (x) -> 
[(0.1*sin(3*Pi*x[1])+0.1*sin(Pi*x[1])+0.4*cos(Pi*x[1]))*sin(2*Pi*x[2])-0.5*sin(4*Pi*x[1])+sin(2*Pi*x[1]), 
  0.2*sin(2*Pi*x[2])*sin(3*Pi*x[1])+2.*cos(2*Pi*x[1])+0.5, 
  0.25*cos(2*Pi*x[2])*sin(2*Pi*x[1])+0.4*cos(2*Pi*x[2])];
