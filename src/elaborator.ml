open Kernel
open Printer

(* Proof terms with holes (= unfinished proofs) *)

type h_proof_term = 
| Hole 
| HEmpty of (sequent*rule)
| HUnary of (sequent*rule*h_proof_term)
| HBinary of (sequent*rule*h_proof_term*h_proof_term)
| HTernary of (sequent*rule*h_proof_term*h_proof_term*h_proof_term)

(* Functions to build proof terms: elaborator of the proof assistant *
The impure functions change the proof state by closing a goal (apply_axiom, apply_top_intro),
changing the first goal (apply_abstraction, apply_orintrol, apply_bottom_elim...), 
generating two subgoals (apply_modus_ponens, apply_and_elim), or three (apply_or_elim) 
They also update the reference to the proof tree with holes: the rightmost hole in the proof 
term is replaced by the rule and its label, with new holes (except for the 
rules which are suppose to terminate a proof) *)

let rec contains_hole = function
    | Hole -> true
    | HEmpty (_, _) -> false
    | HUnary (_, _, h') -> contains_hole h'
    | HBinary (_, _, h1, h2) -> contains_hole h1 || contains_hole h2 
    | HTernary (_, _, h1, h2, h3) -> contains_hole h1 || contains_hole h2 || contains_hole h3

(* This function replace the rightmost hole by a new h_proof_term *)

let rec replace_in_hpt h s r =
    match h with
    | Hole -> begin match r with
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
        end
    | HEmpty(s', r') -> HEmpty (s', r')
    | HUnary(s', r', h') -> HUnary(s', r', replace_in_hpt h' s r)
    | HBinary(s', r', h1, h2) -> 
        if contains_hole h2 then
             HBinary (s', r', h1, replace_in_hpt h2 s r) 
        else HBinary (s', r', replace_in_hpt h1 s r, h2)
    | HTernary (s', r', h1, h2, h3) -> 
        if contains_hole h3 then 
            HTernary (s', r', h1, h2, replace_in_hpt h3 s r) 
        else if contains_hole h2 then
            HTernary (s', r', h1, replace_in_hpt h2 s r, h3) 
        else HTernary (s', r', replace_in_hpt h1 s r, h2, h3)

let tl = function
    | [] -> []
    | x :: xs -> xs

let hd = function
    | [] -> failwith "attempt to compute the head of an empty list"
    | x :: xs -> x

(* Basic tactics : apply the rules of the intuitionnistic logic *)

let apply_axiom prf_st hpt =
    let s = hd !prf_st in
    prf_st := tl !prf_st ; 
    hpt := replace_in_hpt !hpt s Axiom

let apply_abstraction prf_st hpt =
    let s = hd !prf_st in
    let (ctx, t) = s in
    let (a, b) = split_arrow t in 
    let s' = (a::ctx, b) in
    prf_st := s' :: (tl !prf_st) ; 
    hpt := replace_in_hpt !hpt s Abstraction

let apply_modus_ponens prf_st a hpt =
    let s = hd !prf_st in
    let (ctx, b) = s in
    let s1 = (ctx, Arr (a, b)) in
    let s2 = (ctx, a) in
    prf_st := s1 :: s2 :: (tl !prf_st) ; 
    hpt := replace_in_hpt !hpt s ModusPonens

let apply_and_intro prf_st hpt =
    let s = hd !prf_st in
    let (ctx, t) = s in
    let (a, b) = split_and t in 
    let s1=(ctx, a) in
    let s2=(ctx, b) in
    prf_st:= s1::s2:: (tl !prf_st) ; 
    hpt := replace_in_hpt !hpt s AndIntro

let apply_and_elim prf_st f hpt =
    match f with
    | And (a, b) -> 
        let s = hd !prf_st in
        let (ctx, c) = s in
        let s1 = (ctx, f) in
        let s2= (a::b::ctx, c) in
        prf_st := s1::s2:: (tl !prf_st);
        hpt := replace_in_hpt !hpt s AndElim
    | _ -> failwith "the formula eliminated is not a conjunction"

let apply_or_introl prf_st hpt =
    let s = hd !prf_st in
    let (ctx, c) = s in
    let (a, b) = split_or c in
    let s1 = (ctx, a) in
    prf_st := s1 :: (tl !prf_st);
    hpt := replace_in_hpt !hpt s OrIntrol

let apply_or_intror prf_st hpt =
    let s = hd !prf_st in
    let (ctx, c) = s in
    let (a, b) = split_or c in
    let s1 = (ctx, b) in
    prf_st := s1 :: (tl !prf_st);
    hpt := replace_in_hpt !hpt s OrIntror

let apply_or_elim prf_st f hpt =
    match f with
    | Or (a, b) -> 
        let s = hd !prf_st in
        let (ctx, c) = s in
        let s1 = (ctx, f) in
        let s2= (a::ctx, c) in
        let s3= (b::ctx, c) in
        prf_st := s1::s2::s3:: (tl !prf_st);
        hpt := replace_in_hpt !hpt s OrElim
    | _ -> failwith "the formula eliminated is not a disjunction"

let apply_top_intro prf_st hpt = 
    let s = hd !prf_st in
    prf_st := tl !prf_st ; 
    hpt := replace_in_hpt !hpt s TopIntro

let apply_top_elim prf_st hpt = 
    let s = hd !prf_st in
    let (ctx, a) = s in
    let s1 = (Top::ctx, a) in
    prf_st := s1 :: tl !prf_st ; 
    hpt := replace_in_hpt !hpt s TopElim

let apply_bottom_elim prf_st hpt =
    let s = hd !prf_st in
    let (ctx, a) = s in
    let s1 = (ctx, Bottom) in
    prf_st := s1 :: tl !prf_st ; 
    hpt := replace_in_hpt !hpt s BottomElim

(* The proof terms of the kernel are terms which do not contains hole *)

let rec hpt_to_pt = function
    | Hole -> failwith "proof not finished"
    | HEmpty (s, r) -> Empty (s, r)
    | HUnary (s, r, h) -> Unary (s, r, hpt_to_pt h)
    | HBinary (s, r, h1, h2) -> Binary (s, r, hpt_to_pt h1, hpt_to_pt h2)
    | HTernary (s, r, h1, h2, h3) -> Ternary (s, r, hpt_to_pt h1, hpt_to_pt h2, hpt_to_pt h3)
