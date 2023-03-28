open Kernel

(* Printing functions: needed to interact with the user *)

let rec trm_to_string = function 
| Var v -> v
| Arr (t1, t2) -> begin match t1 with 
    | Var v -> Printf.sprintf "%s -> %s" v (trm_to_string t2) 
    |_ -> Printf.sprintf "(%s) -> %s" (trm_to_string t1) (trm_to_string t2)
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
let str = sequent_to_string ([ Var "A" ; Arr (Var "A", Var "B")], (Var "C")) in 
print_string str *)