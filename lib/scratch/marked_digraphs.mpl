# This is from the original version of Gemma Halliwell's thesis.
# It is probably not useful.

`is_element/marked_digraphs` := (V::set) -> (m,n::nonnegint) -> proc(EIO)
 local E,VI,VO,NI,NO,v;
 
 if not (type(EIO,list) and nops(EIO) = 3) then
  return false;
 fi;

 E,VI,VO := op(EIO);

 if not `is_element/digraphs`(V)(E) then
  return false;
 fi;
 
 if not(type(VI,set) and nops(VI) = m and VI minus V = {}) then
  return false;
 fi;

 if not(type(VO,set) and nops(VO) = n and VO minus V = {}) then
  return false;
 fi;

 if VI intersect VO <> {} then return false; fi;

 NI := `in_neighbour_table/digraphs`(V)(E);
 NO := `out_neighbour_table/digraphs`(V)(E);

 for v in VI do
  if nops(NI[v]) <> 0 then return false; fi;
 od:

 for v in VO do
  if nops(NO[v]) <> 0 then return false; fi;
  if nops(NI[v]) <> 1 then return false; fi;
 od:

 return true;
end:

`internal_vertices/marked_digraphs` := (V) -> (m,n) -> proc(EIO)
 local E,VI,VO;
 E,VI,VO := op(EIO);
 return V minus (VI union VO);
end:

