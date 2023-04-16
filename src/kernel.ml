type trm = Var of string 
        | Arr of (trm*trm)
        | And of (trm*trm)
        | Or of (trm*trm) 
        | Top 
        | Bottom

(** Contexts : on paper an arbitrary context is often represented by the variable Γ. 
As it is a list of terms, in OCaml we will use the list notation [A1; ...; An] for the sequent A1, ..., An *)

type context = trm list

(** Sequent : a sequent is a pair between a context and a term, a pair between the hypothesis and the conclusion 
Example: the sequent A -> B, A |- B  would be written ([Arr (Var "A", Var "B"); Var "A"], Var "B") *)

type sequent = context*trm

type goal = sequent list

(* Note: we use general and-elim rule *)
type rule = Axiom | Abstraction | ModusPonens | AndIntro | AndElim | OrIntrol | OrIntror | OrElim | 
            BottomElim | TopIntro | TopElim

type proof_term = 
    | Empty of (sequent*rule) 
    | Unary of (sequent*rule*proof_term) 
    | Binary of (sequent*rule*proof_term*proof_term)

(** We need to check when two terms are equal, so there is a function to implement this equality between terms *)

let rec eq_term t1 t2 =
match t1, t2 with
| Var v1, Var v2 -> String.equal v1 v2
| Arr (t1, t1'), Arr (t2, t2') -> eq_term t1 t2 && eq_term t1' t2'
| And (t1, t1'), Arr (t2, t2') -> eq_term t1 t2 && eq_term t1' t2'
| Or (t1, t1'), Or (t2, t2') -> eq_term t1 t2 && eq_term t1' t2'
| Top, Top -> true
| Bottom, Bottom -> true
| _, _ -> false

let is_arrow = function
| Arr _ -> true
| _ -> false

let is_and = function
| And _ -> true
| _ -> false

let is_or = function 
| Or _ -> true
| _ -> false

let is_top = function
| Top -> true
| _ -> false

let is_bottom = function
| Bottom -> true
| _ -> false 

(** Here, we return a pair between the left of the arrow and its right. 
If the term is not an arrow, it returns an error. 
There are similar functions for others logical connectives. *)

let split_arrow = function
| Arr (t1, t2) -> (t1, t2)
| _ -> failwith "not an arrow"

let split_and = function
| And (t1, t2) -> (t1, t2)
| _ -> failwith "not a conjunction"

let split_or = function
| Or (t1, t2) -> (t1, t2)
| _ -> failwith "not a disjunction"

(* Checks if a term belongs to a list of term. 
Remember: it is useful because in the axiom rule we have a side condition, 
which is precisely that the conclusion must belong to the premises *)

let rec mem t = function
| [] -> false
| x :: xs -> eq_term t x || mem t xs

(** This function removes a term t from a context, 
    and return the context without the first occurence of this term t *)

let rec remove_exn a c = 
if mem a c then 
match c with
| [] -> []
| x :: xs -> if eq_term a x then xs else x :: remove_exn a xs
else failwith "looked for a formula not present in a context"

(** This function implements equalities between context. 
If we go back and look at the modus ponens rule, we note that the contexts should be the same in the two premises and in the conclusion.
Thus, to check a proof tree, we often need to check equalities between contexts. *)

let rec eq_ctx c1 c2 = 
match c1, c2 with
| [], [] -> true
| x1::xs1, x2::xs2 -> eq_term x1 x2 && eq_ctx xs1 xs2
| _, _ -> false

(** This function checks the correction of an application of an axiom rule : the term t must belong to the context l *)

let verif_axiom t l = if mem t l then () else failwith 
"could not apply the axiom: the conclusion of the sequent does not belong to the premises"

(** This function checks the correction of an application of the abstraction rule *)

let verif_abstraction seq1 seq2 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    if is_arrow t1 then 
        let (a, b) = split_arrow t1 in
        if eq_term t2 b then 
            let c2' = remove_exn a c2 in
            if eq_ctx c1 c2' then ()
                else failwith "the upper context does not match to the lower context"
            else failwith "the conclusion of the sequent does not correspond to the right of the arrow"
        else failwith "the abstraction rule was applied on a term which does not contain an arrow"


(** This function checks the correction of an application of the modus ponens rule *)

let verif_modus_ponens seq1 seq2 seq3 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    let (c3, t3) = seq3 in
        if is_arrow t2 then 
        let (a, b) = split_arrow t2 in 
            if eq_term t1 b then 
                if eq_term t3 a then if eq_ctx c1 c2 && eq_ctx c2 c3 then ()
                        else failwith "failure while applying modus ponens: the contexts are different"
                    else failwith "the premise does not match to the antecedent of the implication"
                else if is_arrow t3 then 
        let (a, b) = split_arrow t3 in 
            if eq_term t1 b then 
                if eq_term t2 a then 
                    if eq_ctx c1 c2 && eq_ctx c2 c3 then ()
                        else failwith "failure while applying modus ponens: the contexts are different"
                    else failwith "the premise does not match to the antecedent of the implication"
                else failwith "the conclusion of the sequent does not match to the consequent of the implication"
        else failwith "cannot apply the modus ponens because no premises has an arrow as conclusion"
    else if is_arrow t3 then 
        let (a, b) = split_arrow t3 in 
            if eq_term t1 b then 
                if eq_term t2 a then 
                    if eq_ctx c1 c2 && eq_ctx c2 c3 then ()
                        else failwith "failure while applying modus ponens: the contexts are different"
                    else failwith "the premise does not match to the antecedent of the implication"
                else failwith "the conclusion of the sequent does not match to the consequent of the implication"
        else failwith "cannot apply the modus ponens because no premises has an arrow as conclusion"

(* Verification of AndIntro rule *)

let verif_and_intro seq1 seq2 seq3 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    let (c3, t3) = seq3 in
        let (a, b) = split_and t1 in 
        if eq_ctx c1 c2 && eq_ctx c2 c3 then 
            if (eq_term a t1 && eq_term b t2) || (eq_term a t2 && eq_term a t1) then () 
            else failwith "the and intro-rule was applied with wrong conjuncts"
        else failwith "failure while applying the introduction of and: the contexts are different"

(* Verification of AndElim rule *)
        


(** This functions returns the sequent that we are trying to prove *)

let current_sequent p =
    match p with
    | Empty (s, r) -> s
    | Unary (s, _, _) -> s
    | Binary (s, _, _, _) -> s

(** This is the main function of the kernel : given any proof term, 
it checks each application of the rules, each premise and each conclusion: all of them must be correct application of the given rule. 
If it is the case, it prints "Qed" because the proof is correct, otherwise it returns an error *)

let rec verif_proof_term p =
    match p with
    | Empty (s, r) ->
        begin match r with
        | Axiom -> let (l, a) = s in verif_axiom a l
        | _ -> failwith "the leaves of the proof term could be only labelled by an axiom rule"
        end
    | Unary (s, r, p') ->
        begin match r with
        | Abstraction -> let s' = current_sequent p' in verif_abstraction s s' ; verif_proof_term p'
        | Axiom -> failwith "an axiom has no premises"
        | ModusPonens -> failwith "applying the modus ponens requires two premises"
        end
    | Binary (s, r, p1, p2) ->
        begin match r with
        | ModusPonens -> let s1 = current_sequent p1 in let s2 = current_sequent p2 in let _ = verif_modus_ponens s s1 s2  in 
        let _ = verif_proof_term p1 in verif_proof_term p2 
        | Axiom -> failwith "an axiom has no premises"
        | Abstraction -> failwith "applying the abstraction rule requires only one premise"
        end