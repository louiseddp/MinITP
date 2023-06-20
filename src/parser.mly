%{

  open Lexing
  open Kernel

%}

// Formulae
%token ARROW OR AND
%token <string> IDENT

%token TURNSTILE
%token TOP BOTTOM
%token LPAR RPAR
%token EOF

%right ARROW
%left OR
%left AND

// Rules
%token <int> INT
%token AUTO
%token MODUSPONENS
%token AXIOM
%token ABSTRACTION
%token ANDINTRO
%token ANDELIM
%token ANDELIMLEFT
%token ANDELIMRIGHT
%token ORINTROL
%token ORINTROR
%token ORELIM
%token BOTTOMELIM
%token TOPINTRO
%token TOPELIM
%token COMMUTE
%token ASSERT
%token APPLY
%token IN
%token RENAME
%token INTO

%start seq
%start rule
%type <(int * (Kernel.tactic_arg list  * Kernel.rule))> rule
// %type <(Kernel.tactic_arg list)*(Kernel.rule)> infrule
%type <Kernel.sequent> seq

%%
seq:
  | l=list(formula) TURNSTILE f=formula EOF { (l, f) }
;

formula:
  | TOP                         { Top }
  | BOTTOM                      { Bottom }
  | id=IDENT                    { Var id }
  | LPAR f=formula RPAR         { f }
  | f1=formula ARROW f2=formula { Arr (f1, f2) }
  | f1=formula OR f2=formula    { Or (f1, f2) }
  | f1=formula AND f2=formula   { And (f1, f2) }
;

rule:
  | INT infrule { ($1-1, $2) }
  | infrule     { (0, $1) }
;

infrule:
  | AUTO EOF                          { ([], Auto) }
  | MODUSPONENS f=formula EOF         { ([Term f], ModusPonens) }
  | AXIOM EOF                         { ([], Axiom) }
  | ABSTRACTION EOF                   { ([], Abstraction) }
  | ANDINTRO EOF                      { ([], AndIntro) }
  | ANDELIM f1=formula f2=formula EOF { ([Term f1; Term f2], AndElim) }
  | ANDELIMLEFT f=formula EOF         { ([Term f], AndElimLeft) }
  | ANDELIMRIGHT f=formula EOF        { ([Term f], AndElimRight) }
  | ORINTROL EOF                      { ([], OrIntrol) }
  | ORINTROR EOF                      { ([], OrIntror) }
  | ORELIM f1=formula f2=formula EOF  { ([Term f1; Term f2], OrElim) }
  | TOPELIM EOF                       { ([], TopElim) }
  | TOPINTRO EOF                      { ([], TopIntro) }
  | BOTTOMELIM EOF                    { ([], BottomElim) }
  | COMMUTE EOF                       { ([], Commute) }
  | ASSERT f=formula EOF              { ([Term f], Assert) }
  | APPLY h1=INT IN h2=INT            { ([Index (h1-1); Index (h2-1)], ApplyIn ) }
  | RENAME v1=IDENT INTO v2=IDENT     { ([Term (Var v1); Term (Var v2)], RenameInto)}
;
