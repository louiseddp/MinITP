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
    | Ternary of (sequent*rule*proof_term*proof_term*proof_term)

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
exception Not_in_context

let rec remove_exn a c = 
if mem a c then 
match c with
| [] -> []
| x :: xs -> if eq_term a x then xs else x :: remove_exn a xs
else raise Not_in_context

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
            if (eq_term a t2 && eq_term b t3) || (eq_term b t2 && eq_term a t3) then () 
            else failwith "the and intro-rule was applied with wrong conjuncts"
        else failwith "failure while applying the introduction of and: the contexts are different"

(* Verification of AndElim rule *)

let verif_and_elim seq1 seq2 seq3 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    let (c3, t3) = seq3 in
        if eq_ctx c1 c2 then 
            let (a, b) = split_and t2 in
            let c3' = remove_exn a c3 in
            let c3'' = remove_exn b c3' in
            if eq_ctx c1 c3'' then 
                if eq_term t1 t3 then () 
                else failwith "elimination of and rule made on different formulae"
            else failwith "wrong contexts during the application of and-elim rule"
        else if eq_ctx c1 c3 then 
            let (a, b) = split_and t3 in
            let c2' = remove_exn a c2 in
            let c2'' = remove_exn b c2' in
            if eq_ctx c1 c2'' then 
                if eq_term t1 t2 then () 
                else failwith "elimination of and rule made on different formulae"
            else failwith "wrong contexts during the application of and-elim rule"
        else failwith "wrong contexts during the application of and-elim rule: 
        no context of the premise match the context of the conclusion"

(* Verification of or intro_left and right rules *)

let verif_or_introl seq1 seq2 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    if is_or t1 then 
        let (a, _) = split_or t1 in
        if eq_term a t2 then 
            if eq_ctx c1 c2 then () 
            else failwith "the contexts are not equal: failure during the application of or-intro-left rule"
        else failwith "the formulae does not match: you may try to apply or-intro-r instead or simply the rule is not correct"
    else failwith "application of or-intro-left on a formula which is not an or"

let verif_or_intror seq1 seq2 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    if is_or t1 then 
        let (_, a) = split_or t1 in
        if eq_term a t2 then 
            if eq_ctx c1 c2 then () 
            else failwith "the contexts are not equal: failure during the application of or-intro-right rule"
        else failwith "the formulae does not match: you may try to apply or-intro-l instead or simply the rule is not correct"
    else failwith "application of or-intro-right on a formula which is not an or"

(* Verification of or elimination rule: the implementation is slightly different
   from the other rules; 
   We test that the rule is ok for at least one permutation of the premises *)

let elim_or_ok seq1 seq2 seq3 seq4 =
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
    let (c3, t3) = seq3 in
    let (c4, t4) = seq4 in
        if is_or t2 then
            let (a, b) = split_or t2 in
            if mem a c3 && mem b c4 then 
                let c3' = remove_exn a c3 in
                let c4' = remove_exn b c4 in
                if eq_ctx c1 c2 && eq_ctx c2 c3' && eq_ctx c3' c4' then 
                    if eq_term t1 t3 && eq_term t3 t4 then true
                    else false
                else false
            else false 
        else false

let verif_or_elim seq1 seq2 seq3 seq4 = 
    if
    elim_or_ok seq1 seq2 seq3 seq4 || 
    elim_or_ok seq1 seq2 seq4 seq3 ||
    elim_or_ok seq1 seq3 seq3 seq4 ||
    elim_or_ok seq1 seq3 seq4 seq3 ||
    elim_or_ok seq1 seq4 seq2 seq3 ||
    elim_or_ok seq1 seq4 seq3 seq2
    then ()
    else failwith "failure during the verification of or-elim rule"

(* Verification of Top intro and elim rules *)

let verif_top_intro seq1 = 
    let (c1, t1) = seq1 in
    if is_top t1 then () else failwith "the top rule was applied on a sequent whose conclusion is not top" 

let verif_top_elim seq1 seq2 = 
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
        if eq_term t1 t2 then 
            let c2' = remove_exn Top c2 in
            if eq_ctx c1 c2' then () 
            else failwith "the contexts do not match during the use of top-elim rule"
        else failwith "the conclusions are different during the use of top-elim rule"

(* Verification of bottom_elim *)
let verif_bottom_elim seq1 seq2 = 
    let (c1, t1) = seq1 in
    let (c2, t2) = seq2 in
        if eq_term t2 Bottom then 
            if eq_ctx c1 c2 then ()
            else failwith "the contexts do not match during the use of bottom-elim rule"
        else failwith "bottom is not the conclusion of the premise sequent in the use of the bottom-elim rule"

(** This functions returns the sequent that we are trying to prove *)

let current_sequent p =
    match p with
    | Empty (s, _) -> s
    | Unary (s, _, _) -> s
    | Binary (s, _, _, _) -> s
    | Ternary (s, _, _, _, _) -> s

(** This is the main function of the kernel : given any proof term, 
it checks each application of the rules, each premise and each conclusion: all of them must be correct application of the given rule. 
If it is the case, it prints "Qed" because the proof is correct, otherwise it returns an error *)

let rec verif_proof_term p =
    match p with
    | Empty (s, r) ->
        begin match r with
        | Axiom -> let (l, a) = s in verif_axiom a l
        | TopIntro -> verif_top_intro s
        | _ -> failwith "the leaves of the proof term could be only labelled by an axiom rule or a top-intro rule"
        end
    | Unary (s, r, p') ->
        begin match r with
        | Abstraction -> let s' = current_sequent p' in verif_abstraction s s' ; verif_proof_term p'
        | OrIntrol -> let s' = current_sequent p' in verif_or_introl s s' ; verif_proof_term p'
        | OrIntror -> let s' = current_sequent p' in verif_or_intror s s' ; verif_proof_term p'
        | BottomElim -> let s' = current_sequent p' in verif_bottom_elim s s' ; verif_proof_term p'
        | TopElim -> let s' = current_sequent p' in verif_top_elim s s' ; verif_proof_term p'
        | _ -> failwith "the rule used is not unary but it is a label of an unary node in the proof tree"
        end
    | Binary (s, r, p1, p2) ->  
        let _ = verif_proof_term p1 in 
        let _ = verif_proof_term p2 in
        let s1 = current_sequent p1 in 
        let s2 = current_sequent p2 in
        begin match r with
        | ModusPonens ->  
            verif_modus_ponens s s1 s2 
        | AndIntro -> 
            verif_and_intro s s1 s2
        | AndElim -> 
            verif_and_elim s s1 s2
        | _ -> failwith "the rule used is not binary but it is a label of an unary node in the proof tree"
        end
    | Ternary (s, r, p1, p2, p3) -> 
       begin match r with
        | OrElim -> 
            let s1 = current_sequent p1 in 
            let s2 = current_sequent p2 in 
            let s3 = current_sequent p3 in
            let _ = verif_or_elim s s1 s2 s3 in
            let _ = verif_proof_term p1 in 
            let _ = verif_proof_term p2 in
            verif_proof_term p3
        | _ -> failwith "the only ternary rule is or-elim"
        end