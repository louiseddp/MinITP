(** This file is the kernel : the validity of all the Minlog proof assistant relies on the fact that this file has no bug. 
All the other files depend on it. 
It defines the minimal logic and the meaning of it rules through the functions which allow to verify that a rule was correctly applied.
The main function is `verif_proof_term`. 
Given a proof written in minimal logic, it will say that the proof is correct or if it contains an error *)


(** Terms, context and sequents and goals

- A term is either a variable which can represent any proposition (we call them propositional variables) or a formula composed 
of an arbitrary number of implications between variables. 
For instance, A could stand for the proposition "Socrates is human", B could stand for the proposition "Socrates is mortal".
A -> B would be the proposition "If Socrates is human then Socrates is mortal"
- A context is a list of propositions that we consider as true. The context is the list of our hypothesis. 
It is often represented by the symbol Γ. 
- A sequent is a pair between the context (our hypothesis), and a term which is the conclusion. 
It is usually written A1, ..., Ak |- B
- The goal is the list of sequent that we are trying to prove *)


(** Terms : Var "A" stands for the propositional variable A. The constructor Arr is for building implications from already
given terms 

Examples : the formula (A->B)-> C would be represented as Arr (Arr (Var "A", Var "B"), Var "C").
The formula A->(B->C) would be represented as Arr (Var "A", Arr (Var "B", Var "C")) *)

type trm = Var of string | Arr of (trm*trm)

(** Contexts : on paper an arbitrary context is often represented by the variable Γ. 
As it is a list of terms, in OCaml we will use the list notation [A1; ...; An] for the sequent A1, ..., An *)

type context = trm list

(** Sequent : a sequent is a pair between a context and a term, a pair between the hypothesis and the conclusion 
Example: the sequent A -> B, A |- B  would be written ([Arr (Var "A", Var "B"); Var "A"], Var "B") *)

type sequent = context*trm

type goal = sequent list

(** A rule is composed of its premises, its side conditions and its conclusion. 
We use the notation Γ for any sequent and P for any term.
The premises are a (possibly empty) list of sequents or side conditions: if they are true, then the conclusion is also true. 
The conclusion is always a sequent.
In minimal logic, we have only three rules. 

The axiom rule has no premises but one side condition to be true : P must belong to Γ,and the conclusion is of the form :  Γ |- P 
Indeed, each time we have P among the list of our hypotheses Γ, we know that we can conclude P, we already hold it to be true.

The abstraction rule has one premise : Γ, P |- Q and one conclusion Γ |- P -> Q 
This rules says that whenever Q is true when all the terms in Γ and P are true, then, given all the proposition in Γ, 
we know that P -> Q is true

The modus ponens allows us to use the information contained in the implication.
This rule has two premises : Γ |- P-> Q and Γ |- P and one conclusion Γ |- Q. 
Whenever we have P-> Q and P, we can conclude Q (under the context Γ) 

For now, we only give the name of the rules *)

type rule = Axiom | Abstraction | ModusPonens

(** Definition of the proof term : a tree labelized by a rule.

- Empty should be used on the top of the proof tree, when we use a rule with no premise : here, there is only one such rule, the axiom rule.
- Unary should be used when the rule has one premise : here, there is only one such rule, the abstraction rule.
So, whenever we use the abstraction rule in a proof, we know that we will have to prove a new sequent.
- Binary should be used when the rule has two premises : here, there is only one such rule, the modus ponens. 
So, whenever we use the modus ponens rule, we will have to prove two remaining premises.

However, it is possible to not respect these principle and to write wrong proof trees.
They do not correspond to a valid proof in minimal logic, they are nonsense or at least they contain mistakes. 
But they will be rejected by the function `verif_proof_term`.

As an example of correct proof trees, let us represent how two proof trees would be written on paper and how it will be represented in our implementation. 
On paper, the trivial proof of A |- A would be represented as :


       A ∈ [A]
       ________(axiom)
        A |- A

In our OCaml representation, the proof term is : Empty of (([Var "A"], Var "A"), Axiom).
Indeed, as there is no sequent on top of the sequent A |- A, we use the Empty constructor of the type proof_term. 
The current sequent is ([Var "A"], Var "A") and the side condition  A ∈ [A] will be checked later in the function `verif_axiom`


Let us consider a more complex example : 
On paper, the proof of (A->B)->C, B |- C is : 

                                                B ∈ [(A->B)->C, B, A] 
                                                _____________________   (axiom)
       (A->B)->C ∈ [(A->B)->C, B]               (A->B)->C, B, A |- B
    ______________________________(axiom)       ______________________ (abstraction)      
    (A->B)->C, B |- (A-> B) -> C                (A->B)->C, B |- (A->B)
                ____________________________________________________(modus ponens)
                              (A->B)->C, B |- C
                 
                 
In OCaml, the proof term is quite long. We would use the notation P =  Arr (Arr (Var "A", Var "B"), Var "C") to 
shorten our proof term.

Binary (([P, Var "B"], Var "C"), ModusPonens, Empty (([P; Var "B"], P), Axiom), Unary (([P; Var "B"]), Arr (Var "A", Var "B")), Abstraction, Empty (([P; Var "B"; Var "A"], Var "A"), Axiom)))
*)

type proof_term = Empty of (sequent*rule) | Unary of (sequent*rule*proof_term) | Binary of (sequent*rule*proof_term*proof_term)

(** We need to check when two terms are equal, so there is a function to implement this equality between terms *)

let rec eq_term t1 t2 =
match t1, t2 with
| Var v1, Var v2 -> String.equal v1 v2
| Arr (t1, t1'), Arr (t2, t2') -> eq_term t1 t2 && eq_term t1' t2'
| _, _ -> false

(** Here, we check if a term contains an arrow *)

let is_arrow = function
| Arr _ -> true
| _ -> false

(** Here, we return a pair between the left of the arrow and its right. 
If the term is not an arrow but a variable, the functions return an error *)

let split_arrow = function
| Arr (t1, t2) -> (t1, t2)
| _ -> failwith "not an arrow"

(* Checks if a term belongs to a list of term. 
Remember: it is useful because in the axiom rule we have a side condition, which is precisely that the conclusion must belong to the premises *)

let rec mem t = function
| [] -> false
| x :: xs -> eq_term t x || mem t xs

(** This function removes a term t from a context, and return the context without the first occurence of this term t *)

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

(** This functions returns the sequent that we are trying to prove *)

let current_sequent p =
    match p with
    | Empty (s, r) -> s
    | Unary (s, _, _) -> s
    | Binary (s, _, _, _) -> s

(** This is the main function of the kernel : given any proof term, it checks each application of the rules, each premise and each conclusion: all of them must be correct application of the given rule. 
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