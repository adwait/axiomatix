%{
  open Lexing
%}
%token <int> INT
%token <string> STRING
%token DEFINEMACRO EXPANDMACRO STAGENAME
%token AXIOM
%token MICROOP CORE THREAD
%token READ WRITE RMWREAD RMWWRITE FENCE
%token FORALL EXISTS
%token COMMA PERIOD COLON SEMICOLON QUOTE
%token AND OR NOT IMPLIES IFF
%token LPAREN RPAREN
%token PRED
%token LBRACKET RBRACKET
%token ANYNAME WITH AS
%token EOF
%token PLUS
%token COREID
%token ACCESSED NOTACCESSED ACCESSEDDONTCARE
%token DIRTY NOTDIRTY DIRTYDONTCARE
%nonassoc FORALL EXISTS COMMA
%nonassoc IFF
%right IMPLIES
%right OR
%right AND
%nonassoc NOT
%left PLUS
%start main
%type <USpecLang.microarchitecturalComponent> main
%%

main:
  statements EOF {$1};

statements:
  | statements statement {$1 @ [$2]}
  | statement {[$1]};

statement:
  | axiom {USpecLang.FOLAxiom ($1)}
  | macro {USpecLang.FOLMacroDefinition ($1)}
  | contextterm {USpecLang.FOLContextTerm ($1)};

contextterm:
  STAGENAME INT qstring PERIOD {USpecLang.StageNameTerm($3, $2)};

axiom:
  AXIOM qstring COLON formula PERIOD {USpecLang.FOLName ($2, $4)};

macro:
  | DEFINEMACRO qstring args COLON formula PERIOD
    {USpecLang.Pair(USpecLang.Pair($2, $3), $5)}
  | DEFINEMACRO qstring COLON formula PERIOD
    {USpecLang.Pair(USpecLang.Pair($2, []), $4)}

args:
  | args STRING {$1 @ [$2]}
  | STRING {[$1]};

params:
  | params string_or_int {$1 @ [$2]}
  | string_or_int {[$1]};

qstring:
  | QUOTE str QUOTE {$2}
  | QUOTE QUOTE {""};

str:
  STRING {$1};

formula:
  | LPAREN str COLON formula RPAREN {USpecLang.FOLName ($2, $4)}
  | EXPANDMACRO str params {USpecLang.FOLExpandMacro ($2, $3)}
  | EXPANDMACRO str {USpecLang.FOLExpandMacro ($2, [])}
  | LPAREN formula RPAREN {$2}
  | predicate {USpecLang.FOLPredicate $1}
  | NOT formula {USpecLang.FOLNot $2}
  | formula AND formula {USpecLang.FOLAnd ($1, $3)}
  | formula OR formula {USpecLang.FOLOr ($1, $3)}
  | formula IMPLIES formula {USpecLang.fOLImplies $1 $3}
  | formula IFF formula {USpecLang.fOLIff $1 $3}
  | EXISTS quantifier COMMA formula {USpecLang.FOLExists ($2, $4)}
  | FORALL quantifier COMMA formula {USpecLang.FOLForAll ($2, $4)}
  | WITH MICROOP INT AS qstring COMMA formula
    {
      USpecLang.FOLExists (USpecLang.microopQuantifier($5),
        USpecLang.FOLAnd
          (USpecLang.FOLPredicate(USpecLang.PredHasGlobalID($3, $5)), $7))
    };

quantifier:
  | MICROOP qstring {USpecLang.microopQuantifier($2)}
  | CORE qstring {USpecLang.coreQuantifier($2)};
  | THREAD qstring {USpecLang.threadQuantifier($2)};

accessedStatus:
  | ACCESSED {USpecLang.Accessed}
  | NOTACCESSED {USpecLang.NotAccessed}
  | ACCESSEDDONTCARE {USpecLang.AccessedDontCare};

dirtyStatus:
  | DIRTY {USpecLang.Dirty}
  | NOTDIRTY {USpecLang.NotDirty}
  | DIRTYDONTCARE {USpecLang.DirtyDontCare};

predicate:
  | str INT INT INT INT str {USpecLang.fOLLookupPredicate_IIIIS $1 $2 $3 $4 $5 $6}
  | str str str str {USpecLang.fOLLookupPredicate_SSS $1 $2 $3 $4}
  | str str str {USpecLang.fOLLookupPredicate_SS $1 $2 $3}
  | str accessedStatus dirtyStatus str str
    {USpecLang.fOLLookupPredicate_ADSS $1 $2 $3 $4 $5}
  | str accessedStatus dirtyStatus str
    {USpecLang.fOLLookupPredicate_ADS $1 $2 $3 $4}
  | str INT str {USpecLang.fOLLookupPredicate_IS $1 $2 $3}
  | str str {USpecLang.fOLLookupPredicate_S $1 $2}
  | str edge {USpecLang.fOLLookupPredicate_E $1 $2}
  | str edgelist {USpecLang.fOLLookupPredicate_lE $1 $2}
  | str node {USpecLang.fOLLookupPredicate_N $1 $2}
  | str nodelist {USpecLang.fOLLookupPredicate_lN $1 $2}
  | LPAREN PRED str str RPAREN {USpecLang.fOLLookupPredicate_custom_S $3 $4};

edgelist:
  LBRACKET edges RBRACKET {$2};

edges:
  | edges SEMICOLON edge {$1 @ [$3]}
  | edge {[$1]};

edge:
  | LPAREN node COMMA node COMMA qstring RPAREN
    {
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      USpecLang.Pair(USpecLang.Pair(USpecLang.Pair ($2, $4), linenum ^ ":" ^ $6),
        (* if compare $6 "path" == 0 then "black" else *)
          (
            let a = Random.int 6 in
            let b = Random.int 256 in
            match a with
            | 0 -> Printf.sprintf "#00FF%02x" b
            | 1 -> Printf.sprintf "#00%02xFF" b
            | 2 -> Printf.sprintf "#FF00%02x" b
            | 3 -> Printf.sprintf "#%02x00FF" b
            | 4 -> Printf.sprintf "#FF%02x00" b
            | 5 -> Printf.sprintf "#%02xFF00" b
            | _ -> raise (Failure "random color generation")
          )
      )
    }
  | LPAREN node COMMA node COMMA qstring COMMA qstring RPAREN
    {
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      USpecLang.Pair(USpecLang.Pair(USpecLang.Pair ($2, $4),
        linenum ^ ":" ^ $6), $8)
    };

nodelist:
  LBRACKET nodes RBRACKET {$2};

nodes:
  | nodes SEMICOLON node {$1 @ [$3]}
  | node {[$1]};

node:
  | LPAREN str COMMA LPAREN string_or_int COMMA string_or_int RPAREN RPAREN
    {USpecLang.Pair ($2, USpecLang.Pair ($5, $7))};
  | LPAREN str COMMA string_or_int RPAREN
    {USpecLang.Pair ($2, USpecLang.Pair (USpecLang.SoICoreID $2, $4))};

string_or_int:
  | string_or_int PLUS string_or_int {USpecLang.SoISum ($1, $3)}
  | str {USpecLang.SoIString $1}
  | INT {USpecLang.SoIInt $1}
  | COREID str {USpecLang.SoICoreID $2};
