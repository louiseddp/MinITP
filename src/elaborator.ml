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

let rec replace_in_hpt h s r n =
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

let apply_axiom args n prf_st hpt =
  match args with
  | [] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let l, a = s in
      try
        Kernel.verif_axiom a l;
        let prf_st = new_prf_st in
        let hpt = replace_in_hpt hpt s Axiom n in
        Right (prf_st, hpt)
      with _ -> Left "the formula is not in the context")
  | _ -> Left "the axiom does not take arguments"

let apply_abstraction args n prf_st hpt =
  match args with
  | [] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, t = s in
      try
        let a, b = split_arrow t in
        let s' = (a :: ctx, b) in
        let prf_st = insert_nth n s' new_prf_st in
        let hpt = replace_in_hpt hpt s Abstraction n in
        Right (prf_st, hpt)
      with _ -> Left "the formula is not an arrow")
  | _ -> Left "the abstraction does not take arguments"

(* Equivalent to apply *)
let apply_modus_ponens args n prf_st hpt =
  match args with
  | [ Term a ] ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, b = s in
      let s1 = (ctx, Arr (a, b)) in
      let s2 = (ctx, a) in
      let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st) in
      let hpt = replace_in_hpt hpt s ModusPonens n in
      Right (prf_st, hpt)
  | _ -> Left "the modus ponens takes exactly one term argument"

let apply_and_intro args n prf_st hpt =
  match args with
  | [] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, t = s in
      try
        let a, b = split_and t in
        let s1 = (ctx, a) in
        let s2 = (ctx, b) in
        let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st) in
        let hpt = replace_in_hpt hpt s AndIntro n in
        Right (prf_st, hpt)
      with _ -> Left "the formula is not a conjunction")
  | _ -> Left "the let introduction does not take arguments"

let apply_and_elim args n prf_st hpt =
  match args with
  | [ Term a; Term b ] ->
      let f = And (a, b) in
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, c = s in
      let s1 = (ctx, f) in
      let s2 = (a :: b :: ctx, c) in
      let prf_st = insert_nth n s1 (insert_nth n s2 new_prf_st) in
      let hpt = replace_in_hpt hpt s AndElim n in
      Right (prf_st, hpt)
  | _ -> Left "the let elimination takes exactly two term arguments"

let apply_and_elim_right args n prf_st hpt =
  match args with
  | [ Term f ] -> (
      let s = nth n prf_st in
      let ctx, a = s in
      match apply_and_elim [ Term f; Term a ] n prf_st hpt with
      | Left err -> Left err
      | Right (prf_st', hpt') -> apply_axiom [] (n + 1) prf_st' hpt')
  | _ -> Left "the let left elimination takes exactly one term argument"

let apply_and_elim_left args n prf_st hpt =
  match args with
  | [ Term f ] -> (
      let s = nth n prf_st in
      let ctx, a = s in
      match apply_and_elim [ Term a; Term f ] n prf_st hpt with
      | Left err -> Left err
      | Right (prf_st', hpt') -> apply_axiom [] (n + 1) prf_st' hpt')
  | _ -> Left "the let right elimination takes exactly one term argument"

let apply_or_introl args n prf_st hpt =
  match args with
  | [] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, t = s in
      try
        let a, b = split_or t in
        let s' = (ctx, a) in
        let prf_st = insert_nth n s' new_prf_st in
        let hpt = replace_in_hpt hpt s OrIntrol n in
        Right (prf_st, hpt)
      with _ -> Left "the formula is not a disjunction")
  | _ -> Left "the or left introduction does not take arguments"

let apply_or_intror args n prf_st hpt =
  match args with
  | [] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, t = s in
      try
        let a, b = split_or t in
        let s' = (ctx, b) in
        let prf_st = insert_nth n s' new_prf_st in
        let hpt = replace_in_hpt hpt s OrIntror n in
        Right (prf_st, hpt)
      with _ -> Left "the formula is not a disjunction")
  | _ -> Left "the or right introduction does not take arguments"

let apply_or_elim args n prf_st hpt =
  match args with
  | [ Term a; Term b ] ->
      let f = Or (a, b) in
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, c = s in
      let s1 = (ctx, f) in
      let s2 = (a :: ctx, c) in
      let s3 = (b :: ctx, c) in
      let prf_st =
        insert_nth n s1 (insert_nth n s2 (insert_nth n s3 new_prf_st))
      in
      let hpt = replace_in_hpt hpt s OrElim n in
      Right (prf_st, hpt)
  | _ -> Left "the or elimination takes exactly two term arguments"

let apply_top_intro args n prf_st hpt =
  match args with
  | [] ->
      let s, new_prf_st = pop_nth n prf_st in
      let prf_st = new_prf_st in
      let hpt = replace_in_hpt hpt s TopIntro n in
      Right (prf_st, hpt)
  | _ -> Left "the top introduction does not take arguments"

let apply_top_elim args n prf_st hpt =
  match args with
  | [] ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, a = s in
      let s' = (Top :: ctx, a) in
      let prf_st = insert_nth n s' new_prf_st in
      let hpt = replace_in_hpt hpt s TopElim n in
      Right (prf_st, hpt)
  | _ -> Left "the top elimination does not take arguments"

let apply_bottom_elim args n prf_st hpt =
  match args with
  | [] ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, a = s in
      let s' = (ctx, Bottom) in
      let prf_st = insert_nth n s' new_prf_st in
      let hpt = replace_in_hpt hpt s BottomElim n in
      Right (prf_st, hpt)
  | _ -> Left "the bottom elimination does not take arguments"

let try_apply tactic prf_st hpt =
  if count_holes hpt > 0 then tactic prf_st hpt
  else Left "The proof is already complete"

(* Takes a list of tactics and applies them *)

let rec fold_apply tactics prf_st hpt =
  match tactics with
  | [] -> Right (prf_st, hpt)
  | tactic :: rest -> (
      match try_apply tactic prf_st hpt with
      | Left _ -> fold_apply rest prf_st hpt
      | Right (prf_st', hpt') -> fold_apply tactics prf_st' hpt')

let apply_auto args n prf_st hpt =
  match args with
  | [] ->
      let tactics = [ apply_abstraction [] n; apply_axiom [] n ] in
      fold_apply tactics prf_st hpt
  | _ -> Left "the auto tactic does not take arguments"

let rec fold_apply_once tactics prf_st hpt =
  match tactics with
  | [] -> Right (prf_st, hpt)
  | tactic :: rest -> (
      match try_apply tactic prf_st hpt with
      | Left _ -> fold_apply_once rest prf_st hpt
      | Right (prf_st', hpt') -> fold_apply_once rest prf_st' hpt')

let apply_commute args n prf_st hpt =
  let s, new_prf_st = pop_nth n prf_st in
  let ctx, t = s in
  match t with
  | And (a, b) ->
      fold_apply_once
        [
          apply_and_intro [] n;
          apply_and_elim_right [ Term b ] n;
          apply_and_elim_left [ Term a ] (n + 1);
        ]
        prf_st hpt
  | Or (a, b) ->
      fold_apply_once
        [
          apply_or_elim [ Term b; Term a ] n;
          apply_or_intror [] (n + 1);
          apply_axiom [] (n + 1);
          (* Here we do not use n + 2 because n + 1 was prooven henceforth the hole n + 1 is filled *)
          (* and the hole n + 2 is now n + 1 *)
          apply_or_introl [] (n + 1);
          apply_axiom [] (n + 1);
        ]
        prf_st hpt
  | _ ->
      Left
        "the formula is not a conjunction or a disjunction, could not apply \
         commute"

let apply_assert args n prf_st hpt =
  match args with
  | [ Term a ] ->
      fold_apply_once
        [ apply_modus_ponens [ Term a ] n; apply_abstraction [] n ]
        prf_st hpt
  | _ -> Left "the assert tactic takes exactly one term argument"

let apply_apply_in args n prf_st hpt =
  match args with
  | [ Index i; Index j ] -> (
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, c = s in
      if (i < 1 || i > List.length ctx) && (j < 1 || j > List.length ctx) then
        Left "the indexes are out of bounds"
      else if i = j then Left "the indexes must be different"
      else
        let f, g = (nth i ctx, nth j ctx) in
        match f with
        | Arr (a, b) ->
            if a = g then
              fold_apply_once
                [
                  apply_assert [ Term b ] n;
                  apply_modus_ponens [ Term a ] (n + 1);
                  apply_axiom [] (n + 1);
                  apply_axiom [] (n + 1);
                ]
                prf_st hpt
            else
              Left
                "the term on the left of the arrow does not match the term \
                 applied to"
        | _ -> Left "the first index is not an arrow")
  | _ -> Left "the apply ... in ... tactic takes exactly two arguments"

let any f l = List.fold_left (fun acc x -> acc || f x) false l

let apply_rename_into args n prf_st hpt =
  match args with
  | [ Term (Var v1); Term (Var v2) ] ->
      let s, new_prf_st = pop_nth n prf_st in
      let ctx, t = s in
      let rec var_appears = function
        | Top -> false
        | Bottom -> false
        | Var x -> x = v2
        | Arr (a, b) -> var_appears a || var_appears b
        | And (a, b) -> var_appears a || var_appears b
        | Or (a, b) -> var_appears a || var_appears b
      in
      if any var_appears (t :: ctx) then
        Left "the variable already appears in the context"
      else
        let rec replace_var = function
          | Var v -> if v = v1 then Var v2 else Var v
          | Arr (a, b) -> Arr (replace_var a, replace_var b)
          | And (a, b) -> And (replace_var a, replace_var b)
          | Or (a, b) -> Or (replace_var a, replace_var b)
          | Top -> Top
          | Bottom -> Bottom
        in
        let prf_st =
          insert_nth n (List.map replace_var ctx, replace_var t) new_prf_st
        in
        Right (prf_st, hpt)
  | _ -> Left "the rename ... into ... tactic takes exactly two arguments"

type trigger_var = TGoal | TSomeHyp

type trigger_form =
  (* Variable are removed and replaced by Discard or MetaVar *)
  (* wich can used to get either discard or get the subform *)
  (* | TVar of string *)
  | TArr of trigger_form * trigger_form
  | TAnd of trigger_form * trigger_form
  | TOr of trigger_form * trigger_form
  | TTop
  | TBottom
  | TDiscard
  | TMetaVar

type trigger =
  | TEq of trigger_var * trigger_var
  | TIs of trigger_var * trigger_form
  | TContains of trigger_var * trigger_form

let infix a g c = g a c
let tgoal = TGoal
let tsome_hyp = TSomeHyp
let tarr a b = TArr (a, b)
let tand a b = TAnd (a, b)
let tor a b = TOr (a, b)
let ttop = TTop
let tbottom = TBottom
let tdiscard = TDiscard
let tmetavar = TMetaVar
let teq a b = TEq (a, b)
let tis a b = TIs (a, b)
let tcontains a b = TContains (a, b)
let trigger_axiom = infix tgoal teq tsome_hyp
let trigger_or_elim = infix tsome_hyp tis (tor tmetavar tmetavar)
let trigger_and_intro = infix tgoal tis (tand tdiscard tdiscard)

let interpret_trigger_var prf_st =
  let (hyps, goal), _ = pop_nth 0 prf_st in
  function TGoal -> [ goal ] | TSomeHyp -> hyps

let interpret_teq prf_st a b =
  let a' = interpret_trigger_var prf_st a in
  let b' = interpret_trigger_var prf_st b in
  if List.exists (fun x -> List.mem x a') b' then Some [] else None

let rec interpret_trm_with_trigger_form trm form =
  match (trm, form) with
  | Top, TTop -> Some []
  | Bottom, TBottom -> Some []
  | Arr (a, b), TArr (a', b') -> (
      let a'' = interpret_trm_with_trigger_form a a' in
      let b'' = interpret_trm_with_trigger_form b b' in
      match (a'', b'') with Some x, Some y -> Some (x @ y) | _ -> None)
  | And (a, b), TAnd (a', b') -> (
      let a'' = interpret_trm_with_trigger_form a a' in
      let b'' = interpret_trm_with_trigger_form b b' in
      match (a'', b'') with Some x, Some y -> Some (x @ y) | _ -> None)
  | Or (a, b), TOr (a', b') -> (
      let a'' = interpret_trm_with_trigger_form a a' in
      let b'' = interpret_trm_with_trigger_form b b' in
      match (a'', b'') with Some x, Some y -> Some (x @ y) | _ -> None)
  | meta, TMetaVar -> Some [ meta ]
  | _, TDiscard -> Some []
  | _ -> None

let rec flatten_option_list = function
  | [] -> None
  | None :: xs -> flatten_option_list xs
  | Some x :: xs -> Some x

let interpret_tis prf_st a b =
  let a' = interpret_trigger_var prf_st a in
  let result = List.map (fun x -> interpret_trm_with_trigger_form x b) a' in
  flatten_option_list result

let rec interpret_tcontains prf_st a b =
  let a' = interpret_trigger_var prf_st a in
  let result =
    List.map
      (fun x ->
        match interpret_trm_with_trigger_form x b with
        | None -> (
            match x with
            | Arr (a'', b') | And (a'', b') | Or (a'', b') -> (
                match interpret_trm_with_trigger_form a'' b with
                | None -> interpret_trm_with_trigger_form b' b
                | succes' -> succes')
            | _ -> None)
        | succes -> succes)
      a'
  in
  flatten_option_list result

let rec interpret_trigger prf_st = function
  | TEq (a, b) -> interpret_teq prf_st a b
  | TIs (a, b) -> interpret_tis prf_st a b
  | TContains (a, b) -> interpret_tcontains prf_st a b

let trigered_tactics = Hashtbl.create 16

let rec trigger prf_st hpt =
  let triggers =
    [
      (trigger_axiom, apply_axiom, "Axiom");
      (trigger_or_elim, apply_or_elim, "OrElim");
      (trigger_and_intro, apply_and_intro, "AndIntro");
    ]
  in
  let rec trigger' triggers =
    match triggers with
    | [] -> Left "no trigger found"
    | (option_trigger, tactic, message) :: triggers' -> (
        match interpret_trigger prf_st option_trigger with
        | Some l ->
            if List.length l > 0 && Hashtbl.mem trigered_tactics l then
              trigger' triggers'
            else (
              print_string @@ "Automaticaly applied " ^ message ^ "\n";
              Hashtbl.add trigered_tactics l tactic;
              let l' = List.map (fun x -> Term x) l in
              tactic l' 0 prf_st hpt)
        | None -> trigger' triggers')
  in
  trigger' triggers

let rec hpt_to_pt = function
  | Hole -> failwith "proof not finished"
  | HEmpty (s, r) -> Empty (s, r)
  | HUnary (s, r, h) -> Unary (s, r, hpt_to_pt h)
  | HBinary (s, r, h1, h2) -> Binary (s, r, hpt_to_pt h1, hpt_to_pt h2)
  | HTernary (s, r, h1, h2, h3) ->
      Ternary (s, r, hpt_to_pt h1, hpt_to_pt h2, hpt_to_pt h3)
