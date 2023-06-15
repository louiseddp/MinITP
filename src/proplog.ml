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

and apply_rule rule args n state tree =
  match rule with
  | Auto -> Elaborator.apply_auto args n state tree
  | Axiom -> Elaborator.apply_axiom args n state tree
  | Abstraction -> Elaborator.apply_abstraction args n state tree
  | ModusPonens -> Elaborator.apply_modus_ponens args n state tree
  | AndIntro -> Elaborator.apply_and_intro args n state tree
  | AndElim -> Elaborator.apply_and_elim args n state tree
  | AndElimLeft -> Elaborator.apply_and_elim_left args n state tree
  | AndElimRight -> Elaborator.apply_and_elim_right args n state tree
  | OrIntrol -> Elaborator.apply_or_introl args n state tree
  | OrIntror -> Elaborator.apply_or_intror args n state tree
  | OrElim -> Elaborator.apply_or_elim args n state tree
  | TopIntro -> Elaborator.apply_top_intro args n state tree
  | TopElim -> Elaborator.apply_top_elim args n state tree
  | BottomElim -> Elaborator.apply_bottom_elim args n state tree
  | Commute -> Elaborator.apply_commute args n state tree
  | Assert -> Elaborator.apply_assert args n state tree
  | ApplyIn -> Elaborator.apply_apply_in args n state tree

let empty = function [] -> true | _ -> false

let _ =
  display_intro ();
  let proof_state = ref [ get_goal () ] and proof_tree = ref Hole in
  while not @@ empty !proof_state do
    display_help ();
    let n, (args, rule) = get_rule () in
    (match apply_rule rule args n !proof_state !proof_tree with
    | Left err -> print_string err
    | Right (state, tree) ->
        proof_state := state;
        proof_tree := tree);
    Printf.printf "\nThere are %d remaining goals.\n" (List.length !proof_state);
    goal_to_string !proof_state
  done;
  print_string "Proof finished. Call to the kernel !";
  verif_proof_term @@ hpt_to_pt !proof_tree;
  print_string "\nQED.\n"
