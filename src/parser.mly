%{

  open Lexing
  open Kernel

%}

%token ARROW OR AND
%token <string> IDENT
%token MODUSPONENS ABSTRACTION AXIOM ANDINTRO ANDELIM ORINTROL ORINTROR ORELIM BOTTOMELIM TOPINTRO TOPELIM
%token TURNSTILE
%token TOP BOTTOM
%token LPAR RPAR
%token EOF

%right ARROW
%left OR
%left AND

%start seq
%start infrule 
%type <(Kernel.trm option)*(Kernel.rule)> infrule
%type <Kernel.sequent> seq

%%
seq:
| l=list(formula) TURNSTILE f=formula EOF { (l, f) }
;

formula:
| TOP { Top }
| BOTTOM { Bottom }
| id=IDENT { Var id }
| LPAR f=formula RPAR { f }
| f1=formula ARROW f2=formula { Arr (f1, f2) }
| f1=formula OR f2=formula { Or (f1, f2) }
| f1=formula AND f2=formula { And (f1, f2) }
;

infrule:
| MODUSPONENS f=formula EOF { (Some f, ModusPonens) }
| AXIOM EOF { (None, Axiom) }
| ABSTRACTION EOF { (None, Abstraction) }
| ANDINTRO EOF { (None, AndIntro) }
| ANDELIM f1=formula f2=formula EOF { (Some (And (f1, f2)), AndElim) }
| ORINTROL EOF { (None, OrIntrol) }
| ORINTROR EOF { (None, OrIntror) }
| ORELIM f1=formula f2=formula EOF { (Some (Or (f1, f2)), OrElim) }
| TOPELIM EOF { (None, TopElim) }
| TOPINTRO EOF { (None, TopIntro) }
| BOTTOMELIM EOF {(None, BottomElim) }
;