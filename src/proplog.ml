open Kernel
open Printer
open Elaborator
open Parser
open Lexing
open Lexer

let proof_state : goal ref = ref []

let proof_tree = ref Hole

let proof_finished = ref false

let _ = 
        print_string "Welcome to the PropLog proof assistant. Enter the sequent that you want to prove. \n 
        It should have the form
        A1, ..., An |- B\n
        The Ais contain only propositional variables, parenthesis, arrows, T (as top),
        F (as bottom), conjunction and disjunction\n" ; 
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
            | (None, TopIntro) -> Elaborator.apply_top_intro proof_state proof_tree
            | (None, TopElim) -> Elaborator.apply_top_elim proof_state proof_tree
            | (None, BottomElim) -> Elaborator.apply_bottom_elim proof_state proof_tree
            | _ -> failwith "error while applying a rule" 
        in
        let len = List.length !proof_state in 
        Printf.printf "\nThere are %d remaining goals.\n" len ;
        match !proof_state with
            | [] -> proof_finished := true; 
            print_string "Proof finished. Call to the kernel !" ; 
            let ptree = hpt_to_pt !proof_tree in verif_proof_term ptree s; print_string ("\nQED.\n")
            | x :: xs -> goal_to_string (x :: xs)
        done
