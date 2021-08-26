with(plots):
with(plottools):

great_arc := proc(u,v,hue)
 local w,r,s,t,d,i;
 w := [u[2]*v[3]-u[3]*v[2],u[3]*v[1]-u[1]*v[3],u[1]*v[2]-u[2]*v[1]];
 r := evalf(sqrt(u[1]^2+u[2]^2+u[3]^2));
 d := u[1]*v[1]+u[2]*v[2]+u[3]*v[3];
 w := [v[1] - d * u[1]/r^2,v[2] - d * u[2]/r^2,v[3] - d * u[3]/r^2];
 s := evalf(sqrt(w[1]^2+w[2]^2+w[3]^2));
 w := [r*w[1]/s,r*w[2]/s,r*w[3]/s]; 
 t := evalf(arccos(d/r^2))/10;
 return(CURVES(
        [seq([cos(i*t)*u[1]+sin(i*t)*w[1],
              cos(i*t)*u[2]+sin(i*t)*w[2],
              cos(i*t)*u[3]+sin(i*t)*w[3]],i=0..10)],
        COLOR(HUE,hue))); 
end:

