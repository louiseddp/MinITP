%{

  open Lexing
  open Kernel

%}

%token ARROW
%token <string> IDENT
%token MODUSPONENS ABSTRACTION AXIOM
%token TURNSTILE
%token LPAR RPAR
%token EOF

%right ARROW

%start seq
%start infrule 
%type <(Kernel.trm option)*(Kernel.rule)> infrule
%type <Kernel.sequent> seq

%%
seq:
| l=list(formula) TURNSTILE f=formula EOF { (l, f) }
;

formula:
| id=IDENT { Var id }
| LPAR f=formula RPAR { f }
| f1=formula ARROW f2=formula { Arr (f1, f2) }
;

infrule:
| MODUSPONENS f=formula EOF { (Some f, ModusPonens) }
| AXIOM EOF { (None, Axiom) }
| ABSTRACTION EOF { (None, Abstraction) }
;