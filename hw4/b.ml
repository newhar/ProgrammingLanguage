type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(************************************)
(*      List utility functions      *)
(************************************)
let rec list_length : 'a list -> int
= fun lst ->
  match lst with
  | [] -> 0
  | hd::tl -> 1 + list_length tl

let rec list_exists : ('a -> bool) -> 'a list -> bool
= fun pred lst ->
  match lst with 
  | [] -> false 
  | hd::tl -> if (pred hd) then true else list_exists pred tl

let rec list_fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
= fun func acc lst1 lst2 ->
  match (lst1, lst2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func (func acc hd1 hd2) tl1 tl2
  | _ -> raise (Failure "list_fold2 : two lists have different length")

let rec list_fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold func (func acc hd) tl 

(********************************)
(*     Handling environment     *)
(********************************)
let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if (x = id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if (x = id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)
let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc, v)::tl -> if (l = loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

let size_of_mem mem = 
  let add_if_new x l = if list_exists (fun y -> x = y) l then l else x::l in
  let dom = list_fold (fun dom loc -> add_if_new loc dom) [] mem  in
    list_length dom

(***************************)
(*     Handling record     *)
(***************************)
let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
  | [] -> raise(Failure ("field "^ id ^" is not included in record"))
  | (x, l)::tl -> if (id = x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(******************)
(* Pretty printer *)
(******************)
let rec value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record r -> "{" ^ record2str r ^ "}" 

and record2str : record -> string
= fun record ->
  match record with
  | [] -> ""
  | [(x, l)] -> x ^ "->" ^ string_of_int l
  | (x, l)::tl-> x ^ "->" ^ string_of_int l ^ ", " ^ record2str tl

let mem2str : memory -> string
= fun mem -> 
  let rec aux mem =
    match mem with
    | [] -> ""
    | [(l, v)] -> string_of_int l ^ "->" ^ value2str v
    | (l, v)::tl -> string_of_int l ^ "->" ^ value2str v ^ ", " ^ aux tl
  in
  "[" ^ aux mem ^ "]"

let rec env2str : env -> string
= fun env -> 
  let rec aux env =
    match env with
    | [] -> ""
    | [binding] -> binding2str binding
    | binding::tl -> binding2str binding ^ ", " ^ aux tl
  in
  "[" ^ aux env ^ "]"

and binding2str : binding -> string
= fun binding ->
  match binding with
  | LocBind (x, l) -> x ^ "->" ^ string_of_int l
  | ProcBind (x, proc) -> x ^ "->" ^ "(" ^ proc2str proc ^ ")"

and proc2str : proc -> string
= fun (xs, e, env) ->  
  let rec args2str xs =
    match xs with
    | [] -> ""
    | [x] -> x
    | x::tl -> x ^ ", " ^ args2str tl
  in
  "(" ^ args2str xs ^ ")" ^ ", E" ^ ", " ^ env2str env

(***************************)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  let mem = gc env mem in
  match e with
  | WRITE e -> 
    let (v1, mem1) = eval env mem e in
    let _ = print_endline (value2str v1) in
    (v1, mem1)
  | NUM n -> (Num(n), mem)
  | TRUE -> (Bool(true), mem) 
  | FALSE -> (Bool(false), mem)
  | UNIT -> (Unit, mem)
  | VAR x ->
    let l = lookup_loc_env x env in
    let v = lookup_mem l mem in
    (v, mem)
  | ADD (e1, e2) -> eval_aop env mem e1 e2 (+)
  | SUB (e1, e2) -> eval_aop env mem e1 e2 (-)
  | MUL (e1, e2) -> eval_aop env mem e1 e2 ( * )
  | DIV (e1, e2) ->
  begin
  let (v1, mem1) = eval env mem e1 in
   let (v2, mem2) = eval env mem1 e2 in
   match (v1, v2) with
   | (Num n1, Num n2) -> 
      if n2 = 0 then raise (Failure ("divide by 0"))
      else (Num (n1 / n2), mem2)
   | _ -> raise UndefinedSemantics
  end
  | EQUAL (e1, e2) -> 
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    begin
      match (v1, v2) with
      | (Num n1, Num n2) -> (Bool(n1 = n2), mem2)
      | (Bool b1, Bool b2) -> (Bool(b1 = b2), mem2)
      | (Unit, Unit) -> (Bool(true), mem2)
      | _ -> raise UndefinedSemantics
    end
  | LESS (e1, e2) -> 
      let (v1, mem1) = eval env mem e1 in
      let (v2, mem2) = eval env mem1 e2 in
      begin
        match (v1, v2) with
        | (Num n1, Num n2) -> (Bool(n1 < n2), mem2)
        | _ -> raise UndefinedSemantics
      end
  | NOT e -> 
    let (x, mem1) = eval env mem e in
    begin
      match x with
      | Bool b -> (Bool(not b), mem1)
      | _ -> raise UndefinedSemantics
    end
  | SEQ (e1, e2) -> 
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    (v2, mem2)    
  | IF (e1, e2, e3) -> 
    let (b, mem1) = eval env mem e1 in
    begin
      match b with
      | Bool true -> let (v, mem2) = eval env mem1 e2 in (v, mem2)
      | Bool false -> let (v, mem2) = eval env mem1 e3 in (v, mem2)
      | _ -> raise UndefinedSemantics
    end 
  | WHILE (e1, e2) ->
    let (b, mem') = eval env mem e1 in
    begin
      match b with
      | Bool true -> let (v1, mem1) = eval env mem' e2 in
                        let (v2, mem2) = eval env mem1 (WHILE(e1, e2)) in
                          (v2, mem2)
      | Bool false -> (Unit, mem')
      | _ -> raise UndefinedSemantics
    end
  | LETV (x, e1, e2) ->
    let (v, mem1) = eval env mem e1 in
    let l = new_location() in
    let (v', mem2) = eval (extend_env (LocBind(x,l)) env) (extend_mem (l, v) mem1) e2 in
      (v', mem2)
  | LETF (f, x_list, e1, e2) -> 
    let (v, mem1) = eval (extend_env (ProcBind(f, (x_list, e1, env))) env) mem e2 in 
      (v, mem1)
  | CALLV (f, exp_list) ->
      let (x_list, e', env') = lookup_proc_env f env in
      let _ = if (List.length exp_list != List.length x_list) then (raise UndefinedSemantics) in 
      let fold (env_acc, mem_acc) x exp = 
        let v, m' = eval env mem_acc exp in
        let l = new_location() in
        ((extend_env (LocBind(x, l)) env_acc) , (extend_mem (l,v) m')) in     
      let (env'', mem'') = list_fold2 fold (env', mem) x_list exp_list in
      let env''' = extend_env (ProcBind(f, (x_list, e', env'))) env'' in
      eval env''' mem'' e'
  | CALLR (f, y_list) ->
      let x_list, e, env' = lookup_proc_env f env in
      let fold env_acc x y = (extend_env (LocBind(x, lookup_loc_env y env)) env_acc) in
      let env'' = list_fold2 fold env' x_list y_list in
      let env''' = extend_env (ProcBind(f, (x_list, e, env'))) env'' in
      eval env''' mem e
  | RECORD lst ->
  (
    match lst with
    | [] -> (Unit, mem)
    | _ -> let (rs, ms) = update_r lst env mem empty_mem empty_record in
    (rs, ms)
  )
  | FIELD (e1, x) -> 
    let (r, mem') = eval env mem e1 in
    begin
    match r with
    | Record r' -> ((lookup_mem (lookup_record x r') mem'), mem')
    | _ -> raise UndefinedSemantics
    end
  | ASSIGN (x, e1) ->
    let (v, mem') = eval env mem e1 in
    let l = lookup_loc_env x env in
      (v, extend_mem (l,v) mem')
  | ASSIGNF (e1, x, e2) ->
    let (r, mem1) = eval env mem e1 in
    let (v, mem2) = eval env mem1 e2 in
    begin
      match r with
      | Record r' -> (v, (extend_mem ((lookup_record x r'), v) mem2))
      | _ -> raise UndefinedSemantics
    end

  and update_r
  =fun lst env mem m_ r_ ->
    match lst with
    | [] -> (Record r_, (helper_fun mem m_))
    | (x, e)::tl -> 
  (
   let (v, m) = eval env mem e in
   let l = new_location() in
   update_r tl env m (extend_mem (l, v) m_) (extend_record (x, l) r_)
  )
  
  and helper_fun
  =fun mem1 mem2 ->
    match mem2 with
    | [] -> mem1
    | (l, v)::tl -> helper_fun (extend_mem (l, v) mem1) tl


and gc : env -> memory -> memory
= fun env mem -> mem (* TODO *)
  (* begin
    match env with 
    | (id,loc)::tl -> 
        let rec search_mem id mem' = 
        if (list_exists loc mem)
  end *)
let runb : exp -> value 
= fun exp ->
  let (v, m) = eval empty_env empty_mem exp in 
  let _ = print_endline ("memory size: " ^ string_of_int (size_of_mem m)) in
    v;;

let ex1 = LETV ("ret", NUM 1,
LETV ("n", NUM 5,
SEQ (
WHILE (LESS (NUM 0, VAR "n"),
SEQ (
ASSIGN ("ret", MUL (VAR "ret", VAR "n")),
ASSIGN ("n", SUB (VAR "n", NUM 1))
)
),
VAR "ret")));;

let ex2 = LETF ("f", ["x1"; "x2"],
SEQ (
ASSIGN ("x1", NUM 3),
ASSIGN ("x2", NUM 3)
),
LETV("x1", NUM 1,
LETV("x2", NUM 1,
SEQ(
CALLR ("f", ["x1"; "x2"]),
ADD(VAR "x1", VAR "x2")))));;

let ex3 = LETV ("f", RECORD ([("x", NUM 10); ("y", NUM 13)]),
LETF ("swap", ["a"; "b"],
LETV ("temp", VAR "a",
SEQ (
ASSIGN ("a", VAR "b"),
ASSIGN ("b", VAR "temp"))),
SEQ (
CALLV("swap", [FIELD (VAR "f", "x"); FIELD (VAR "f", "y")]),
FIELD (VAR "f", "x")
)
)
);;