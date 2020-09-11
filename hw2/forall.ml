let rec forall f l =
  match l with
  | [] -> true
  | hd::tl -> if (f hd = true) then forall f tl else false;;
