{

  open Lexing
  open Parser

  exception Lexing_error of string

  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [ "ModusPonens",   MODUSPONENS;
        "Axiom",   AXIOM;
        "Abstraction",   ABSTRACTION;
      ] ;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT(s)
}

let alpha = ['a'-'z' 'A'-'Z']
let ident = alpha+

rule token = parse 
| ident as id 
    { keyword_or_ident id }
| [' ' '\t' '\r']+
    { token lexbuf }
| "," 
    { token lexbuf }
| "->"
    { ARROW }
| "|-"
    { TURNSTILE }
| "("
    { LPAR }
| ")"
    { RPAR }
| "\n"
    { EOF }
| eof
    { EOF }
| _ { raise (Lexing_error ("unknown character : " ^ (lexeme lexbuf))) }