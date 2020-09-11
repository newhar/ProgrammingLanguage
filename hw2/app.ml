let rec append l1 l2 =
  match l1 with
  | h :: t -> append t (l2@[h])
  | [] -> l2;;
  (* l1의 last element 를 빼는식으로 재귀탐색 하면됨  *)

let rec is_duplicated n l =
  match l with 
  |[] -> false
  |hd::tl -> if ( hd = n ) then true else is_duplicated n tl;;

let rec app l1 l2 =
  match l1 with
  | hd :: tl -> if (is_duplicated hd l2 = true) then app tl l2 else app tl (l2@[hd]) 
  | [] -> l2;;
  (* 아니면 l1 , l2 각각 reverse 하고 그이후 마지막에 reverse할까 ? *)