type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

let rec let_maker e l 
= match e with
  | CONST n -> e
  | VAR x -> 
    (match l with (x', le) -> if (x' = x) then le else e  )
  | ADD (e1,e2) -> ADD (let_maker e1 l, let_maker e2 l)
  | SUB (e1,e2) -> SUB (let_maker e1 l, let_maker e2 l)
  | MUL (e1,e2) -> MUL (let_maker e1 l, let_maker e2 l)
  | DIV (e1,e2) -> DIV (let_maker e1 l, let_maker e2 l)
  | ISZERO e0 -> ISZERO (let_maker e0 l)
  | READ -> e
  | IF (e1,e2,e3) -> IF (let_maker e1 l, let_maker e2 l, let_maker e3 l)
  | LET (x,e1,e2) -> LET (x, let_maker e1 l, let_maker e2 l)
  | LETREC (x,y,e1,e2) -> LETREC (x,y,let_maker e1 l, let_maker e2 l)
  | PROC (x,e0) -> PROC (x, let_maker e0 l)
  | CALL (e1,e2) -> CALL (let_maker e1 l, let_maker e2 l)

let rec expand : exp -> exp 
= fun e -> 
match e with
| CONST n -> e
| VAR x -> e
| ADD (e1,e2) -> ADD (expand e1, expand e2)
| SUB (e1,e2) -> SUB (expand e1, expand e2)
| MUL (e1,e2) -> MUL (expand e1, expand e2)
| DIV (e1,e2) -> DIV (expand e1, expand e2)
| ISZERO e0 -> ISZERO (expand e0)
| READ -> e
| IF (e1,e2,e3) -> IF (expand e1, expand e2, expand e3)
| LET (x,e1,e2) -> 
  let exp' = let_maker e2 (x,e1) in
  if (exp' = e2) then LET (x, expand e1, expand e2) else expand exp'
| LETREC (x,y,e1,e2) -> LETREC (x,y,expand e1, expand e2)
| PROC (x,e0) -> PROC (x, expand e0)
| CALL (e1,e2) -> CALL (expand e1, expand e2) 
;;

(*let ex1 = LET ("x", CONST 1, VAR "x");;*)
(*let ex2 = *)
(*  LET ("f", PROC ("x", VAR "x"), *)
(*    IF (CALL (VAR "f", ISZERO (CONST 0)), *)
(*        CALL (VAR "f", CONST 11), *)
(*        CALL (VAR "f", CONST 22)));;*)
(*let ex3 = LET ("x", ADD (CONST 1, ISZERO (CONST 0)), CONST 2);; *)
(**)
(*expand ex1;;*)
(*expand ex2;;*)