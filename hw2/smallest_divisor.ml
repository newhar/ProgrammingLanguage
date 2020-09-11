let smallest_divisor : int -> int
= fun n -> (*TODO*)
  let n = n in
  let rec is_divided_by d =
    if (d*d > n) then n
    else if (n mod d = 0) then d
    else (is_divided_by (d+1)) in
    is_divided_by 2;;