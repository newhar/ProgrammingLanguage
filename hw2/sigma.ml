let rec sigma f a b =
  (* raise failure b < a *)
  if (a=b) then (f a) 
  else (f a) + (sigma f (a+1) b);;
