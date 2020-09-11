type graph = (vertex * vertex) list
and vertex = int;;

let reverse list =
      let rec helper templist = function
      | [] -> templist
      | hd::tl -> helper (hd::templist) tl
      in helper [] list;;

let rec insert a l =
  match l with 
  | [] -> [a]
  | hd::tl -> if a < hd then a::hd::tl
              else hd::(insert a tl);;

let rec sort l =
  match l with
  | [] -> []
  | hd::tl -> insert hd (sort tl);;

let rec is_visited node list =
      match list with
      | [] -> false
      | hd::tl -> if (hd = node) then true else is_visited node tl;;

let rec successors n = function
| [] -> []
| (s, t) :: edges -> if s = n then t :: successors n edges
                              else  successors n edges;;

let reach : graph * vertex -> vertex list 
= fun (edges, start) ->
  let rec dfs edges visited = function
  | [] -> sort (reverse visited)
  | n::nodes -> if is_visited n visited then dfs edges visited nodes
                                    else dfs edges (n::visited) ((successors n edges) @ nodes) in
                                    dfs edges [] [start];;
(* sort 해야되나 ? *)