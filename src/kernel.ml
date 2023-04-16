Module Kernel

type term = 
        | TVar of string (* named variables *)
        | TTrue of term 
        | TFalse of term
        | TZero of term
        | TSucc of term*term
        | TFun of string*ty*term
        | TApp of term * term
        | TEqIntro of ty*term (* eq_refl A x *)
        | TLeibniz of ty*term*term*term (* the type in which t = u, the term t, the term u, the elimination predicate P *)
        | TBottomElim of term
        | TForallIntro of term
        | TForallElim of term 
        | TLeIntro1 of term (* n <= n *)
        | TLeIntro2 of term*term*term (* forall n m, n <= m -> n <= S m *)
        | TLeElim of term*term*term (* TLeElim P n m : implements the rule
                                    if n <= m -> P and n = 0 -> P and n <= m -> n <= S m -> P then P*)
        | TEq of ty*term*term (* The term associated to the equality type. In a logic like Coq, it would be the same term *)
        | TLe of term*term (* The term associated to the le type. In a logic like Coq, it would be the same term. *)
and ty = 
        | TyNat of ty
        | TyProp of ty
        | TyEq of ty*term*term
        | TyLe of term*term
        | TyBool of ty
        | TyArr of ty*ty
        | TyForall of string*ty*ty
        | TyVar of string

type context = (term*ty) list

type sequent = context*term

type goal = sequent list

type variables = (string list) ref

(* Generates fresh names for variables. 
This function should be improved because it produces ugly names
once 2 has been reached *)

let rec fresh_name_aux (s : string) l l' = 
    match l with
     | [] -> s
     | x :: xs -> 
        if s = x then 
            if String.contains s '0' then 
                if String.contains s '1' then
                fresh_name_aux (s^"2") l l'  else 
            fresh_name_aux (s^"1") l l' else
        fresh_name_aux (s^"0") l l' else 
        fresh_name_aux s xs l'

let fresh_name s l = fresh_name_aux s l l 

let s = fresh_name "x" []

let s1 = fresh_name "x" ["x"]

let s2 = fresh_name "x0" ["x0"; "y"]

(* Checks if s is free in t *) 
let rec is_free_in_trm_aux s t b =
    match t with
    | TVar s' -> if s = s' then if b then true else false else false
    | TTrue -> false
    | TFalse -> false
    | TZero -> false
    | TSucc t' -> is_free_in_trm_aux s t' b
    | TFun (s', ty, t') -> if s = s' then is_free_in_trm_aux s t' false
    | TApp (t1, t2) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b
    | TyEqIntro (ty, t') -> is_free_in_trm_aux s t' b 
    | TLeibniz (ty, t1, t2, t3) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b || is_free_in_trm_aux s t3 b
    | TBottomElim t' -> is_free_in_trm_aux s t' b
    | TForallIntro t' -> is_free_in_trm_aux s t' b
    | TForallElim t' -> is_free_in_trm_aux s t' b 
    | TLeIntro1 t' -> is_free_in_trm_aux s t' b
    | TLeIntro2 (t1, t2, t3) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b || is_free_in_trm_aux s t3 b
    | TLeElim (t1, t2, t3) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b || is_free_in_trm_aux s t3 b
    | TEq of (ty, t1, t2) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b
    | TLe of (t1, t2) -> is_free_in_trm_aux s t1 b || is_free_in_trm_aux s t2 b

let is_free_in_trm s t = is_free_in_trm_aux s t true

let is_free_in_ty aux s t b = 

(* Substitutes the variable represented by the string s by t2 in t1 
To avoid capture, we suppose that the rule that each binder should use a fresh name is followed.
Otherwise, this function may introduce bugs *)
let subst_in_trm t1 t2 s =
    match t1 with 



let subst_in_ty t1 t2 s = 