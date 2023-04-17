open Kernel

(* Printing functions: needed to interact with the user 
  Priorities: And > Or > Arr 
  And and Or are left-associative 
  Arr is right-associative *)

let rec trm_to_string = function 
| Var v -> v
| Top -> "T" 
| Bottom -> "F"
| Arr (t1, t2) -> begin match t1 with 
    | Arr (_, _) -> 
        Printf.sprintf "(%s) -> %s" (trm_to_string t1) (trm_to_string t2)
    | Or (_, _) | And (_, _) | Var _ | Top | Bottom -> 
        Printf.sprintf "%s -> %s" (trm_to_string t1) (trm_to_string t2)
    end
| And (t1, t2) -> begin match t2 with
    | And (_, _) | Arr (_, _) | Or (_, _) -> 
        begin match t1 with
        | Arr (_, _) | Or (_, _)->
            Printf.sprintf "(%s) /\\ (%s)" (trm_to_string t1) (trm_to_string t2)
        | _ -> Printf.sprintf "%s /\\ (%s)" (trm_to_string t1) (trm_to_string t2)
        end
    | _ ->  begin match t1 with
        | Arr (_, _) | Or (_, _)->
            Printf.sprintf "(%s) /\\ %s" (trm_to_string t1) (trm_to_string t2)
        | _ -> Printf.sprintf "%s /\\ %s" (trm_to_string t1) (trm_to_string t2)
        end
    end
| Or (t1, t2) -> begin match t2 with
    | Arr (_, _) | Or (_, _) -> 
        begin match t1 with
        | Arr (_, _) -> Printf.sprintf "(%s) \\/ (%s)" (trm_to_string t1) (trm_to_string t2)
        | _ -> Printf.sprintf "(%s) \\/ %s" (trm_to_string t1) (trm_to_string t2)
        end
    | _ -> begin match t1 with
        | Arr (_, _) -> Printf.sprintf "(%s) \\/ %s" (trm_to_string t1) (trm_to_string t2)
        | _ -> Printf.sprintf "%s \\/ %s" (trm_to_string t1) (trm_to_string t2)
        end
    end 

let remove_last_char =
fun s -> let len = String.length s in String.sub s 0 (len-2)

let context_to_string = 
fun l ->remove_last_char ( (List.fold_right (fun t acc -> Printf.sprintf "%s, %s" (trm_to_string t) acc) l ""))

let sequent_to_string = fun (l, x) -> 
Printf.sprintf "%s |- %s" (context_to_string l) (trm_to_string x)

let rec goal_to_string = function
    | [] -> ()
    | x :: xs -> print_string ((sequent_to_string x)^"\n") ; goal_to_string xs

(* let _ = 
let str = sequent_to_string 
([ And (Or (Top, Bottom), Arr (And (Var "A", Var "C"), And (Var "C", Var "B")))], (Var "C")) in 
print_string str *)