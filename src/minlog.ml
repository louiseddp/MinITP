open Kernel
open Printer
open Elaborator
open Parser
open Lexing
open Lexer

let proof_state : goal ref = ref []

let proof_tree = ref Hole

let proof_finished = ref false

(*
Debug functions 

let verif_modus_ponens_debug seq1 seq2 seq3 =
    let (c1, t1) = seq1 in let str1 = sequent_to_string seq1 in print_string ("\nSequent verified seq1:"^str1^"\n") ;
    let (c2, t2) = seq2 in let str2 = sequent_to_string seq2 in print_string ("\nSequent verified seq2:"^str2^"\n") ;
    let (c3, t3) = seq3 in let str3 = sequent_to_string seq3 in print_string ("\nSequent verified seq3:"^str3^"\n") ;
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

let rec verif_proof_term_debug p =
    match p with
    | Empty (s, r) -> let str = sequent_to_string s in print_string ("\nSequent verified:"^str^"\n") ;
        begin match r with
        | Axiom -> let (l, a) = s in verif_axiom a l
        | _ -> failwith "the leaves of the proof term could be only labelled by an axiom rule"
        end
    | Unary (s, r, p') -> let str = sequent_to_string s in print_string ("Sequent verified:"^str^"\n") ;
        begin match r with
        | Abstraction -> let s' = current_sequent p' in let str' = sequent_to_string s' in print_string ("\nSequent above:"^str'^"\n") ; verif_abstraction s s' ; verif_proof_term_debug p'
        | Axiom -> failwith "an axiom has no premises"
        | ModusPonens -> failwith "applying the modus ponens requires two premises"
        end
    | Binary (s, r, p1, p2) -> let str = sequent_to_string s in print_string ("Sequent verified:"^str^"\n") ;
        begin match r with
        | ModusPonens -> let s1 = current_sequent p1 in let s2 = current_sequent p2 in let _ = verif_modus_ponens_debug s s1 s2  in 
        let _ = verif_proof_term_debug p1 in verif_proof_term_debug p2 
        | Axiom -> failwith "an axiom has no premises"
        | Abstraction -> failwith "applying the abstraction rule requires only one premise"
        end

        *)

let _ = 
        print_string "Welcome to the LogMin proof assistant. Enter the sequent that you want to prove. \n 
        It should have the form
        A1, ..., An |- B\n
        The Ais contain only propositional variables, parenthesis and arrows\n" ; 
        let s = read_line () in 
        let l = (Lexing.from_string s) in 
        let s = Parser.seq Lexer.token l in
        proof_state := s :: !proof_state ; (* goal_to_string !proof_state *)
        while not (!proof_finished) do
        print_string "What is the next step of your proof ?\n
        You can :\n
        - Apply an axiom rule by writing 'Axiom'\n
        - Apply the modus ponens on a formula A by writing 'ModusPonens A'\n
        - Apply the abstraction rule by writing 'Abstraction'\n
        - Apply the and introduction rule by writing 'AndIntro'\n
        - Apply the and elimination rule with the two conjuncts A and B by writing 'AndElim A B'\n
        - Apply the or introduction left rule by writing 'OrIntrol'\n
        - Apply the or introduction right rule by writing 'OrIntror'\n
        - Apply the or elimination rule with the two disjuncts A and B by writing 'OrElim A B'\n
        - Apply the bottom elimination rule by writing 'BottomElim'\n
        - Apply the top introduction rule by writing 'TopIntro'\n
        - Apply the top elimination rule by writing 'TopElim'\n" ;
        let s1 = read_line () in
        let l1 = (Lexing.from_string s1) in
        let r = Parser.infrule Lexer.token l1 in
        let _ =  match r with
            | (None, Axiom) -> Elaborator.apply_axiom proof_state proof_tree
            | (None, Abstraction) -> Elaborator.apply_abstraction proof_state proof_tree
            | (Some f, ModusPonens) -> Elaborator.apply_modus_ponens proof_state f proof_tree
            | (None, AndIntro) -> Elaborator.apply_and_intro proof_state proof_tree
            | (Some f, AndElim) -> Elaborator.apply_and_elim proof_state f proof_tree
            | (None, OrIntrol) -> Elaborator.apply_or_introl proof_state proof_tree
            | (None, OrIntror) -> Elaborator.apply_or_intror proof_state proof_tree
            | (Some f, OrElim) -> Elaborator.apply_or_elim proof_state f proof_tree
            | _ -> failwith "error while applying a rule" 
        in
        let len = List.length !proof_state in 
        Printf.printf "\nThere are %d remaining goals.\n" len ;
        match !proof_state with
            | [] -> proof_finished := true; 
            print_string "Proof finished. Call to the kernel !" ; 
            let ptree = hpt_to_pt !proof_tree in verif_proof_term ptree; print_string ("\nQED.\n")
            | x :: xs -> goal_to_string (x :: xs)
        done
