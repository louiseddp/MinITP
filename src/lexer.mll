{

  open Lexing
  open Parser

  exception Lexing_error of string

  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [
        "Auto",         AUTO;
        "ModusPonens",  MODUSPONENS;
        "Axiom",        AXIOM;
        "Abstraction",  ABSTRACTION;
        "AndIntro",     ANDINTRO;
        "AndElim",      ANDELIM;
        "AndElimLeft",  ANDELIMLEFT;
        "AndElimRight", ANDELIMRIGHT;
        "OrIntrol",     ORINTROL;
        "OrIntror",     ORINTROR;
        "OrElim",       ORELIM;
        "BottomElim",   BOTTOMELIM;
        "TopIntro",     TOPINTRO;
        "TopElim",      TOPELIM;
        "T",            TOP;
        "F",            BOTTOM;
        "Commute",      COMMUTE;
        "Assert",       ASSERT;
        "Apply",        APPLY;
        "in",           IN;
        "Rename",       RENAME;
        "into",         INTO;
      ] ;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT(s)
}

let alpha = ['a'-'z' 'A'-'Z']
let ident = alpha+

let digit = ['0'-'9']
let number = digit+

rule token = parse
| number as n       { INT (int_of_string n) }
| ident as id       { keyword_or_ident id }
| [' ' '\t' '\r']+  { token lexbuf }
| ","               { token lexbuf }
| "->"              { ARROW }
| "/\\"             { AND }
| "\\/"             { OR }
| "|-"              { TURNSTILE }
| "("               { LPAR }
| ")"               { RPAR }
| "\n"              { EOF }
| eof               { EOF }
| _ { raise (Lexing_error ("unknown character : " ^ (lexeme lexbuf))) }
