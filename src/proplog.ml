open Kernel
open Printer
open Elaborator
open Parser
open Lexing
open Lexer

let display_intro () =
  print_string
    "Welcome to the PropLog proof assistant. Enter the sequent that you want \
     to prove. \n\n\
    \        It should have the form\n\
    \        A1, ..., An |- B\n\n\
    \        The Ais contain only propositional variables, parenthesis, \
     arrows, T (as top),\n\
    \        F (as bottom), conjunction and disjunction\n"

and display_help () =
  print_string
    "What is the next step of your proof ?\n\n\
    \        You can :\n\n\
    \        - Apply an axiom rule by writing 'Axiom'\n\n\
    \        - Apply the modus ponens on a formula A by writing 'ModusPonens \
     A'\n\n\
    \        - Apply the abstraction rule by writing 'Abstraction'\n\n\
    \        - Apply the and introduction rule by writing 'AndIntro'\n\n\
    \        - Apply the and elimination rule with the two conjuncts A and B \
     by writing 'AndElim A B'\n\n\
    \          Or use the left or right rule by writing 'AndElimLeft A' or \
     'AndElimRight B'\n\n\
    \        - Apply the or introduction left rule by writing 'OrIntrol'\n\n\
    \        - Apply the or introduction right rule by writing 'OrIntror'\n\n\
    \        - Apply the or elimination rule with the two disjuncts A and B by \
     writing 'OrElim A B'\n\n\
    \        - Apply the bottom elimination rule by writing 'BottomElim'\n\n\
    \        - Apply the top introduction rule by writing 'TopIntro'\n\n\
    \        - Apply the top elimination rule by writing 'TopElim'\n"

let get_goal () =
  let s = read_line () in
  let l = Lexing.from_string s in
  Parser.seq Lexer.token l

and get_rule () =
  let s = read_line () in
  let l = Lexing.from_string s in
  Parser.rule Lexer.token l

and apply_rule state tree n r =
  match r with
  | None, Axiom -> Elaborator.apply_axiom state tree n
  | None, Abstraction -> Elaborator.apply_abstraction state tree n
  | Some f, ModusPonens -> Elaborator.apply_modus_ponens state f tree n
  | None, AndIntro -> Elaborator.apply_and_intro state tree n
  | Some f, AndElim -> Elaborator.apply_and_elim state f tree n
  | Some f, AndElimLeft -> Elaborator.apply_and_elim_left state f tree n
  | Some f, AndElimRight -> Elaborator.apply_and_elim_right state f tree n
  | None, OrIntrol -> Elaborator.apply_or_introl state tree n
  | None, OrIntror -> Elaborator.apply_or_intror state tree n
  | Some f, OrElim -> Elaborator.apply_or_elim state f tree n
  | None, TopIntro -> Elaborator.apply_top_intro state tree n
  | None, TopElim -> Elaborator.apply_top_elim state tree n
  | None, BottomElim -> Elaborator.apply_bottom_elim state tree n
  | _ -> None

let empty = function [] -> true | _ -> false

let _ =
  display_intro ();
  let proof_state = ref [ get_goal () ] and proof_tree = ref Hole in
  while not @@ empty !proof_state do
    display_help ();
    let n, r = get_rule () in
    (match apply_rule !proof_state !proof_tree n r with
    | None -> print_string "Invalid rule.\n"
    | Some (state, tree) ->
        proof_state := state;
        proof_tree := tree);
    Printf.printf "\nThere are %d remaining goals.\n" (List.length !proof_state);
    goal_to_string !proof_state
  done;
  print_string "Proof finished. Call to the kernel !";
  verif_proof_term @@ hpt_to_pt !proof_tree;
  print_string "\nQED.\n"
