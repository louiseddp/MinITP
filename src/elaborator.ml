open Kernel
open Printer
open Either

(* Proof terms with holes (= unfinished proofs) *)

type h_proof_term =
  | Hole
  | HEmpty of (sequent * rule)
  | HUnary of (sequent * rule * h_proof_term)
  | HBinary of (sequent * rule * h_proof_term * h_proof_term)
  | HTernary of (sequent * rule * h_proof_term * h_proof_term * h_proof_term)

type error = String of string | Fallback of goal * h_proof_term

(* Functions to build proof terms: elaborator of the proof assistant *
   The impure functions change the proof state by closing a goal (apply_axiom, apply_top_intro),
   changing the first goal (apply_abstraction, apply_orintrol, apply_bottom_elim...),
   generating two subgoals (apply_modus_ponens, apply_and_elim), or three (apply_or_elim)
   They also update the reference to the proof tree with holes: the rightmost hole in the proof
   term is replaced by the rule and its label, with new holes (except for the
   rules which are suppose to terminate a proof) *)

let rec count_holes = function
  | Hole -> 1
  | HEmpty (_, _) -> 0
  | HUnary (_, _, h') -> count_holes h'
  | HBinary (_, _, h1, h2) -> count_holes h1 + count_holes h2
  | HTernary (_, _, h1, h2, h3) ->
      count_holes h1 + count_holes h2 + count_holes h3

(* This function replace the rightmost hole by a new h_proof_term *)

and replace_in_hpt h s r n =
  match h with
  | Hole -> (
      match r with
      | Axiom -> HEmpty (s, r)
      | Abstraction -> HUnary (s, r, Hole)
      | ModusPonens -> HBinary (s, r, Hole, Hole)
      | AndIntro -> HBinary (s, r, Hole, Hole)
      | AndElim -> HBinary (s, r, Hole, Hole)
      | OrIntrol -> HUnary (s, r, Hole)
      | OrIntror -> HUnary (s, r, Hole)
      | OrElim -> HTernary (s, r, Hole, Hole, Hole)
      | BottomElim -> HUnary (s, r, Hole)
      | TopIntro -> HEmpty (s, r)
      | TopElim -> HUnary (s, r, Hole)
      | _ -> failwith "the rule could not replace a hole")
  | HEmpty (s', r') -> HEmpty (s', r')
  | HUnary (s', r', h') -> HUnary (s', r', replace_in_hpt h' s r n)
  | HBinary (s', r', h1, h2) ->
      let nb_holes = count_holes h2 in
      if n < nb_holes then HBinary (s', r', h1, replace_in_hpt h2 s r n)
      else HBinary (s', r', replace_in_hpt h1 s r (n - nb_holes), h2)
  | HTernary (s', r', h1, h2, h3) ->
      let nb_holes = count_holes h3 in
      let nb_holes' = count_holes h2 + nb_holes in
      if n < nb_holes then HTernary (s', r', h1, h2, replace_in_hpt h3 s r n)
      else if n < nb_holes' then
        HTernary (s', r', h1, replace_in_hpt h2 s r (n - nb_holes), h3)
      else HTernary (s', r', replace_in_hpt h1 s r (n - nb_holes'), h2, h3)

let tl = function [] -> [] | x :: xs -> xs

let hd = function
  | [] -> failwith "attempt to compute the head of an empty list"
  | x :: xs -> x

let rec nth n = function
  | [] -> failwith "index out of range"
  | x :: xs -> if n = 0 then x else nth (n - 1) xs

let rec pop_nth n l =
  match l with
  | [] -> failwith "index out of range"
  | x :: xs ->
      if n = 0 then (x, xs)
      else
        let y, ys = pop_nth (n - 1) xs in
        (y, x :: ys)

let rec insert_nth n x l =
  match l with
  | [] -> [ x ]
  | y :: ys -> if n = 0 then x :: l else y :: insert_nth (n - 1) x ys

(* Basic tactics : apply the rules of the intuitionnistic logic *)
let print_error s =
  print_string "Error: ";
  print_string s;
  print_newline ();
  print_string "The goals are left unchanged."

let apply_axiom prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let l, a = s in
  try
    Kernel.verif_axiom a l;
    let prf_st = new_prf_st and hpt = replace_in_hpt hpt s Axiom n in
    Right (prf_st, hpt)
  with _ -> Left (String "the formula is not in the context")

let apply_abstraction prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, t = s in
  try
    let a, b = split_arrow t in
    let s' = (a :: ctx, b) in
    let prf_st = insert_nth n s' new_prf_st
    and hpt = replace_in_hpt hpt s Abstraction n in
    Right (prf_st, hpt)
  with _ -> Left (String "the formula is not an arrow")

let apply_modus_ponens prf_st a hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, b = s in
  let s1 = (ctx, Arr (a, b)) and s2 = (ctx, a) in
  let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st)
  and hpt = replace_in_hpt hpt s ModusPonens n in
  Right (prf_st, hpt)

let apply_and_intro prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, t = s in
  try
    let a, b = split_and t in
    let s1 = (ctx, a) and s2 = (ctx, b) in
    let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st)
    and hpt = replace_in_hpt hpt s AndIntro n in
    Right (prf_st, hpt)
  with _ -> Left (String "the formula is not a conjunction")

let apply_and_elim prf_st f hpt n =
  match f with
  | And (a, b) ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, c = s in
      let s1 = (ctx, f) and s2 = (a :: b :: ctx, c) in
      let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st)
      and hpt = replace_in_hpt hpt s AndElim n in
      Right (prf_st, hpt)
  | _ -> Left (String "the formula eliminated is not a conjunction")

let apply_and_elim_left prf_st f hpt n =
  let s = nth n prf_st in
  let ctx, a = s in
  match apply_and_elim prf_st (And (f, a)) hpt n with
  | Left err -> Left err
  | Right (prf_st', hpt') -> apply_axiom prf_st' hpt' (n + 1)

let apply_and_elim_right prf_st f hpt n =
  let s = nth n prf_st in
  let ctx, a = s in
  match apply_and_elim prf_st (And (a, f)) hpt n with
  | Left err -> Left err
  | Right (prf_st', hpt') -> apply_axiom prf_st' hpt' (n + 1)

let apply_or_introl prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, t = s in
  try
    let a, b = split_or t in
    let s' = (ctx, a) in
    let prf_st = insert_nth n s' new_prf_st
    and hpt = replace_in_hpt hpt s OrIntrol n in
    Right (prf_st, hpt)
  with _ -> Left (String "the formula is not a disjunction")

let apply_or_intror prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, t = s in
  try
    let a, b = split_or t in
    let s' = (ctx, b) in
    let prf_st = insert_nth n s' new_prf_st
    and hpt = replace_in_hpt hpt s OrIntror n in
    Right (prf_st, hpt)
  with _ -> Left (String "the formula is not a disjunction")

let apply_or_elim prf_st f hpt n =
  match f with
  | Or (a, b) ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, c = s in
      let s1 = (ctx, f) in
      let s2 = (a :: ctx, c) in
      let s3 = (b :: ctx, c) in
      let prf_st =
        insert_nth n s1 (insert_nth n s2 (insert_nth n s3 new_prf_st))
      and hpt = replace_in_hpt hpt s OrElim n in
      Right (prf_st, hpt)
  | _ -> Left (String "the formula eliminated is not a disjunction")

let apply_top_intro prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let prf_st = new_prf_st and hpt = replace_in_hpt hpt s TopIntro n in
  Right (prf_st, hpt)

let apply_top_elim prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, a = s in
  let s' = (Top :: ctx, a) in
  let prf_st = insert_nth n s' new_prf_st
  and hpt = replace_in_hpt hpt s TopElim n in
  Right (prf_st, hpt)

let apply_bottom_elim prf_st hpt n =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, a = s in
  let s' = (ctx, Bottom) in
  let prf_st = insert_nth n s' new_prf_st
  and hpt = replace_in_hpt hpt s BottomElim n in
  Right (prf_st, hpt)

let try_apply tactic prf_st hpt n =
  match tactic prf_st hpt n with
  | Left _ -> Left (Fallback (prf_st, hpt))
  | Right (prf_st', hpt') -> Right (prf_st', hpt')
(* Takes a list of tactics and applies them *)

let rec fold_apply tactics prf_st hpt n =
  match tactics with
  | [] -> Right (prf_st, hpt)
  | tactic :: rest -> (
      match try_apply tactic prf_st hpt n with
      | Left _ -> fold_apply rest prf_st hpt n
      | Right (prf_st', hpt') -> fold_apply tactics prf_st' hpt' n)

and apply_auto prf_st hpt n =
  let tactics = [ apply_abstraction; apply_axiom ] in
  fold_apply tactics prf_st hpt n

(* The proof terms of the kernel are terms which do not contains hole *)

let rec hpt_to_pt = function
  | Hole -> failwith "proof not finished"
  | HEmpty (s, r) -> Empty (s, r)
  | HUnary (s, r, h) -> Unary (s, r, hpt_to_pt h)
  | HBinary (s, r, h1, h2) -> Binary (s, r, hpt_to_pt h1, hpt_to_pt h2)
  | HTernary (s, r, h1, h2, h3) ->
      Ternary (s, r, hpt_to_pt h1, hpt_to_pt h2, hpt_to_pt h3)
