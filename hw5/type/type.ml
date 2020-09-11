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

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
= fun tenv e ty ->
  match e with
  | CONST n -> [(ty, TyInt)]
  | VAR x -> [(ty, tenv x)]
  | ADD (e1,e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | SUB (e1,e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt) 
  | MUL (e1,e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | DIV (e1,e2) -> [(ty, TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | ISZERO n -> [(ty, TyBool)] @ (gen_equations tenv n TyInt)
  | READ -> [(ty,TyInt)]
  | IF (e1,e2,e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
  | LET (x,e1,e2) -> 
    let ty' = fresh_tyvar() in
    let tenv' = TEnv.extend (x, ty') tenv in
    (gen_equations tenv e1 ty') @ (gen_equations tenv' e2 ty)
  | LETREC (f,x,e1,e2) ->
    let ty' = fresh_tyvar() in
    let ty'' = fresh_tyvar() in
    let tenv' = TEnv.extend (f, TyFun (ty',ty'')) tenv in
    let tenv'' = TEnv.extend (x,ty') tenv' in
    (gen_equations tenv'' e1 ty'') @ (gen_equations tenv' e2 ty)
  | PROC (x,e) -> 
    let ty' = fresh_tyvar() in
    let ty'' = fresh_tyvar() in
    let tenv' = TEnv.extend (x, ty') tenv in
    [(ty, TyFun (ty',ty''))] @ (gen_equations tenv' e ty'')
  | CALL (e1,e2) ->
    let ty' = fresh_tyvar() in
    (gen_equations tenv e1 (TyFun (ty', ty))) @ (gen_equations tenv e2 ty')

let solve : typ_eqn -> Subst.t
=fun eqns -> 
  let rec occur_check : string -> typ -> bool
    = fun x t ->
    match t with
    | TyVar y -> x = y
    | TyFun(a,b) -> (occur_check x a) || (occur_check x b)
    | _ -> false  
  in

  let rec unify : typ -> typ -> Subst.t -> Subst.t
  = fun t1 t2 s ->
  match (t1,t2,s) with
  | (TyBool,TyBool,s) -> s
  | (TyInt,TyInt,s) -> s
  | (TyVar x,t,s) -> if occur_check x t then raise(Failure "TypeError")  else Subst.extend x t s
  | (t,TyVar x, s) -> unify (TyVar x) t s
  | (TyFun(t1,t2), TyFun(t3,t4),s) -> let s' = unify t1 t3 s in unify (Subst.apply t2 s') (Subst.apply t4 s') s'
  | (_,_,_) -> raise(Failure "TypeError")
  in

  let rec unification : typ_eqn -> Subst.t -> Subst.t
  = fun eq st -> 
  match eq with
  | [] -> st
  | (t1,t2)::tl -> unification tl (unify (Subst.apply t1 st) (Subst.apply t2 st) st)
  in
  unification eqns Subst.empty 

let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;

(* let ex1 = PROC ("f",
PROC ("x", SUB (CALL (VAR "f", CONST 3),
CALL (VAR "f", VAR "x"))));;

let ex2 = LET ("x", CONST 1,
IF (VAR "x", SUB (VAR "x", CONST 1), CONST 0));; *)