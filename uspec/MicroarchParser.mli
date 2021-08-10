type token =
  | INT of (int)
  | STRING of (string)
  | DEFINEMACRO
  | EXPANDMACRO
  | STAGENAME
  | AXIOM
  | MICROOP
  | CORE
  | THREAD
  | READ
  | WRITE
  | RMWREAD
  | RMWWRITE
  | FENCE
  | FORALL
  | EXISTS
  | COMMA
  | PERIOD
  | COLON
  | SEMICOLON
  | QUOTE
  | AND
  | OR
  | NOT
  | IMPLIES
  | IFF
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | ANYNAME
  | WITH
  | AS
  | EOF
  | PLUS
  | COREID
  | ACCESSED
  | NOTACCESSED
  | ACCESSEDDONTCARE
  | DIRTY
  | NOTDIRTY
  | DIRTYDONTCARE

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> USpecLang.microarchitecturalComponent
