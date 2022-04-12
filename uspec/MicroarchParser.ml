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
  | PRED
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

open Parsing;;
let _ = parse_error;;
# 2 "MicroarchParser.mly"
  open Lexing
# 51 "MicroarchParser.ml"
let yytransl_const = [|
  259 (* DEFINEMACRO *);
  260 (* EXPANDMACRO *);
  261 (* STAGENAME *);
  262 (* AXIOM *);
  263 (* MICROOP *);
  264 (* CORE *);
  265 (* THREAD *);
  266 (* READ *);
  267 (* WRITE *);
  268 (* RMWREAD *);
  269 (* RMWWRITE *);
  270 (* FENCE *);
  271 (* FORALL *);
  272 (* EXISTS *);
  273 (* COMMA *);
  274 (* PERIOD *);
  275 (* COLON *);
  276 (* SEMICOLON *);
  277 (* QUOTE *);
  278 (* AND *);
  279 (* OR *);
  280 (* NOT *);
  281 (* IMPLIES *);
  282 (* IFF *);
  283 (* LPAREN *);
  284 (* RPAREN *);
  285 (* PRED *);
  286 (* LBRACKET *);
  287 (* RBRACKET *);
  288 (* ANYNAME *);
  289 (* WITH *);
  290 (* AS *);
    0 (* EOF *);
  291 (* PLUS *);
  292 (* COREID *);
  293 (* ACCESSED *);
  294 (* NOTACCESSED *);
  295 (* ACCESSEDDONTCARE *);
  296 (* DIRTY *);
  297 (* NOTDIRTY *);
  298 (* DIRTYDONTCARE *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* STRING *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\006\000\004\000\
\005\000\005\000\009\000\009\000\010\000\010\000\007\000\007\000\
\012\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\008\000\008\000\008\000\008\000\014\000\014\000\
\014\000\015\000\015\000\015\000\016\000\016\000\016\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\018\000\021\000\021\000\017\000\017\000\
\020\000\022\000\022\000\019\000\019\000\011\000\011\000\011\000\
\011\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\001\000\001\000\001\000\004\000\005\000\
\006\000\005\000\002\000\001\000\002\000\001\000\003\000\002\000\
\001\000\005\000\003\000\002\000\003\000\001\000\002\000\003\000\
\003\000\003\000\003\000\004\000\004\000\007\000\002\000\002\000\
\002\000\001\000\001\000\001\000\001\000\001\000\001\000\006\000\
\004\000\003\000\005\000\004\000\003\000\002\000\002\000\002\000\
\002\000\002\000\005\000\003\000\003\000\001\000\007\000\009\000\
\003\000\003\000\001\000\009\000\005\000\003\000\001\000\001\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\066\000\000\000\003\000\
\004\000\005\000\006\000\000\000\000\000\000\000\000\000\001\000\
\002\000\017\000\016\000\000\000\012\000\000\000\000\000\000\000\
\000\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\022\000\011\000\000\000\007\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\023\000\000\000\000\000\
\000\000\000\000\010\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\034\000\035\000\036\000\000\000\000\000\047\000\
\048\000\049\000\050\000\000\000\008\000\064\000\000\000\000\000\
\000\000\063\000\031\000\032\000\033\000\000\000\000\000\000\000\
\021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\045\000\000\000\000\000\000\000\054\000\059\000\000\000\000\000\
\000\000\037\000\038\000\039\000\000\000\009\000\065\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\052\000\000\000\057\000\041\000\000\000\062\000\
\051\000\018\000\000\000\000\000\000\000\000\000\000\000\000\000\
\053\000\058\000\043\000\000\000\040\000\000\000\061\000\000\000\
\000\000\000\000\000\000\000\000\000\000\055\000\000\000\000\000\
\060\000\056\000"

let yydgoto = "\002\000\
\006\000\007\000\008\000\009\000\010\000\011\000\013\000\033\000\
\023\000\072\000\073\000\034\000\035\000\044\000\063\000\101\000\
\064\000\065\000\066\000\067\000\095\000\096\000"

let yysindex = "\023\000\
\179\255\000\000\045\255\060\255\045\255\000\000\001\000\000\000\
\000\000\000\000\000\000\006\255\012\255\045\255\056\255\000\000\
\000\000\000\000\000\000\069\255\000\000\163\255\015\255\073\255\
\163\255\000\000\076\255\087\255\087\255\163\255\159\255\103\255\
\220\255\049\255\000\000\000\000\163\255\000\000\226\255\011\255\
\045\255\045\255\045\255\090\255\097\255\000\000\076\255\242\255\
\082\255\125\255\000\000\163\255\163\255\163\255\163\255\051\255\
\003\255\108\255\000\000\000\000\000\000\076\255\244\255\000\000\
\000\000\000\000\000\000\232\255\000\000\000\000\076\255\011\255\
\092\255\000\000\000\000\000\000\000\000\163\255\163\255\076\255\
\000\000\163\255\104\255\121\255\035\255\002\000\002\000\143\255\
\000\000\076\255\130\255\135\255\000\000\000\000\036\255\040\255\
\076\255\000\000\000\000\000\000\076\255\000\000\000\000\092\255\
\011\255\147\255\147\255\128\255\249\255\045\255\152\255\079\255\
\137\255\139\255\000\000\137\255\000\000\000\000\076\255\000\000\
\000\000\000\000\145\255\076\255\011\255\005\255\154\255\137\255\
\000\000\000\000\000\000\163\255\000\000\250\254\000\000\045\255\
\147\255\011\255\057\255\094\255\045\255\000\000\148\255\149\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\175\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\184\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\193\255\
\123\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\114\255\074\255\248\254\253\254\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\202\255\000\000\000\000\000\000\000\000\000\000\000\000\132\255\
\000\000\080\255\085\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\211\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\100\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\173\000\000\000\000\000\000\000\251\255\247\255\
\000\000\000\000\186\255\248\255\000\000\152\000\000\000\000\000\
\201\255\000\000\205\255\000\000\000\000\000\000"

let yytablesize = 286
let yytable = "\015\000\
\016\000\104\000\093\000\020\000\018\000\092\000\094\000\018\000\
\024\000\026\000\138\000\070\000\018\000\021\000\027\000\039\000\
\036\000\026\000\040\000\026\000\046\000\048\000\049\000\001\000\
\027\000\062\000\019\000\068\000\105\000\090\000\022\000\074\000\
\135\000\037\000\120\000\075\000\076\000\077\000\080\000\105\000\
\062\000\126\000\084\000\085\000\086\000\087\000\071\000\089\000\
\091\000\056\000\018\000\088\000\018\000\097\000\134\000\114\000\
\052\000\053\000\129\000\116\000\014\000\127\000\103\000\074\000\
\130\000\012\000\115\000\140\000\106\000\107\000\117\000\108\000\
\109\000\141\000\025\000\057\000\092\000\018\000\058\000\070\000\
\018\000\091\000\056\000\018\000\142\000\059\000\060\000\061\000\
\118\000\026\000\038\000\025\000\119\000\041\000\042\000\043\000\
\074\000\029\000\025\000\025\000\082\000\025\000\028\000\074\000\
\123\000\125\000\078\000\029\000\057\000\050\000\131\000\058\000\
\028\000\079\000\071\000\133\000\074\000\030\000\059\000\060\000\
\061\000\143\000\137\000\014\000\014\000\083\000\105\000\030\000\
\105\000\074\000\139\000\024\000\013\000\013\000\057\000\144\000\
\024\000\110\000\024\000\024\000\014\000\024\000\052\000\111\000\
\014\000\014\000\112\000\014\000\014\000\013\000\014\000\113\000\
\124\000\013\000\013\000\121\000\013\000\013\000\014\000\013\000\
\018\000\132\000\027\000\090\000\018\000\128\000\027\000\013\000\
\052\000\053\000\136\000\054\000\055\000\028\000\029\000\145\000\
\146\000\028\000\029\000\017\000\045\000\003\000\030\000\004\000\
\005\000\031\000\030\000\047\000\000\000\031\000\000\000\032\000\
\020\000\000\000\000\000\032\000\020\000\020\000\000\000\020\000\
\020\000\046\000\020\000\000\000\000\000\046\000\046\000\000\000\
\046\000\046\000\019\000\046\000\000\000\000\000\019\000\019\000\
\000\000\019\000\019\000\042\000\019\000\000\000\000\000\042\000\
\042\000\000\000\042\000\042\000\044\000\042\000\000\000\000\000\
\044\000\044\000\000\000\044\000\044\000\051\000\044\000\000\000\
\000\000\052\000\053\000\069\000\054\000\055\000\000\000\052\000\
\053\000\102\000\054\000\055\000\000\000\052\000\053\000\000\000\
\054\000\055\000\000\000\003\000\000\000\004\000\005\000\052\000\
\053\000\000\000\054\000\055\000\000\000\081\000\052\000\053\000\
\000\000\054\000\055\000\000\000\122\000\000\000\000\000\052\000\
\053\000\000\000\054\000\098\000\099\000\100\000"

let yycheck = "\005\000\
\000\000\072\000\058\000\012\000\002\001\057\000\058\000\002\001\
\014\000\018\001\017\001\001\001\002\001\002\001\018\001\025\000\
\002\001\026\001\027\000\028\001\030\000\031\000\031\000\001\000\
\028\001\034\000\021\001\037\000\035\001\027\001\019\001\040\000\
\028\001\019\001\105\000\041\000\042\000\043\000\047\000\035\001\
\049\000\112\000\052\000\053\000\054\000\055\000\036\001\056\000\
\057\000\001\001\002\001\001\001\002\001\062\000\125\000\020\001\
\022\001\023\001\114\000\020\001\001\001\113\000\071\000\072\000\
\116\000\021\001\031\001\138\000\078\000\079\000\031\001\080\000\
\082\000\017\001\019\001\027\001\128\000\002\001\030\001\001\001\
\002\001\090\000\001\001\002\001\028\001\037\001\038\001\039\001\
\097\000\021\001\018\001\018\001\101\000\007\001\008\001\009\001\
\105\000\018\001\025\001\026\001\019\001\028\001\018\001\112\000\
\110\000\027\001\017\001\028\001\027\001\007\001\119\000\030\001\
\028\001\017\001\036\001\124\000\125\000\018\001\037\001\038\001\
\039\001\028\001\132\000\001\001\002\001\001\001\035\001\028\001\
\035\001\138\000\136\000\018\001\001\001\002\001\027\001\141\000\
\023\001\034\001\025\001\026\001\018\001\028\001\022\001\001\001\
\022\001\023\001\017\001\025\001\026\001\018\001\028\001\017\001\
\001\001\022\001\023\001\028\001\025\001\026\001\036\001\028\001\
\002\001\017\001\004\001\027\001\002\001\027\001\004\001\036\001\
\022\001\023\001\017\001\025\001\026\001\015\001\016\001\028\001\
\028\001\015\001\016\001\007\000\029\000\003\001\024\001\005\001\
\006\001\027\001\024\001\029\001\255\255\027\001\255\255\033\001\
\018\001\255\255\255\255\033\001\022\001\023\001\255\255\025\001\
\026\001\018\001\028\001\255\255\255\255\022\001\023\001\255\255\
\025\001\026\001\018\001\028\001\255\255\255\255\022\001\023\001\
\255\255\025\001\026\001\018\001\028\001\255\255\255\255\022\001\
\023\001\255\255\025\001\026\001\018\001\028\001\255\255\255\255\
\022\001\023\001\255\255\025\001\026\001\018\001\028\001\255\255\
\255\255\022\001\023\001\018\001\025\001\026\001\255\255\022\001\
\023\001\018\001\025\001\026\001\255\255\022\001\023\001\255\255\
\025\001\026\001\255\255\003\001\255\255\005\001\006\001\022\001\
\023\001\255\255\025\001\026\001\255\255\028\001\022\001\023\001\
\255\255\025\001\026\001\255\255\028\001\255\255\255\255\022\001\
\023\001\255\255\025\001\040\001\041\001\042\001"

let yynames_const = "\
  DEFINEMACRO\000\
  EXPANDMACRO\000\
  STAGENAME\000\
  AXIOM\000\
  MICROOP\000\
  CORE\000\
  THREAD\000\
  READ\000\
  WRITE\000\
  RMWREAD\000\
  RMWWRITE\000\
  FENCE\000\
  FORALL\000\
  EXISTS\000\
  COMMA\000\
  PERIOD\000\
  COLON\000\
  SEMICOLON\000\
  QUOTE\000\
  AND\000\
  OR\000\
  NOT\000\
  IMPLIES\000\
  IFF\000\
  LPAREN\000\
  RPAREN\000\
  PRED\000\
  LBRACKET\000\
  RBRACKET\000\
  ANYNAME\000\
  WITH\000\
  AS\000\
  EOF\000\
  PLUS\000\
  COREID\000\
  ACCESSED\000\
  NOTACCESSED\000\
  ACCESSEDDONTCARE\000\
  DIRTY\000\
  NOTDIRTY\000\
  DIRTYDONTCARE\000\
  "

let yynames_block = "\
  INT\000\
  STRING\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statements) in
    Obj.repr(
# 34 "MicroarchParser.mly"
                 (_1)
# 329 "MicroarchParser.ml"
               : USpecLang.microarchitecturalComponent))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statements) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 37 "MicroarchParser.mly"
                         (_1 @ [_2])
# 337 "MicroarchParser.ml"
               : 'statements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 38 "MicroarchParser.mly"
              ([_1])
# 344 "MicroarchParser.ml"
               : 'statements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'axiom) in
    Obj.repr(
# 41 "MicroarchParser.mly"
          (USpecLang.FOLAxiom (_1))
# 351 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'macro) in
    Obj.repr(
# 42 "MicroarchParser.mly"
          (USpecLang.FOLMacroDefinition (_1))
# 358 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'contextterm) in
    Obj.repr(
# 43 "MicroarchParser.mly"
                (USpecLang.FOLContextTerm (_1))
# 365 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 46 "MicroarchParser.mly"
                               (USpecLang.StageNameTerm(_3, _2))
# 373 "MicroarchParser.ml"
               : 'contextterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 49 "MicroarchParser.mly"
                                     (USpecLang.FOLName (_2, _4))
# 381 "MicroarchParser.ml"
               : 'axiom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'qstring) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'args) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 53 "MicroarchParser.mly"
    (USpecLang.Pair(USpecLang.Pair(_2, _3), _5))
# 390 "MicroarchParser.ml"
               : 'macro))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 55 "MicroarchParser.mly"
    (USpecLang.Pair(USpecLang.Pair(_2, []), _4))
# 398 "MicroarchParser.ml"
               : 'macro))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 58 "MicroarchParser.mly"
                (_1 @ [_2])
# 406 "MicroarchParser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 59 "MicroarchParser.mly"
           ([_1])
# 413 "MicroarchParser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'params) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 62 "MicroarchParser.mly"
                         (_1 @ [_2])
# 421 "MicroarchParser.ml"
               : 'params))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 63 "MicroarchParser.mly"
                  ([_1])
# 428 "MicroarchParser.ml"
               : 'params))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    Obj.repr(
# 66 "MicroarchParser.mly"
                    (_2)
# 435 "MicroarchParser.ml"
               : 'qstring))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "MicroarchParser.mly"
                ("")
# 441 "MicroarchParser.ml"
               : 'qstring))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 70 "MicroarchParser.mly"
         (_1)
# 448 "MicroarchParser.ml"
               : 'str))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 73 "MicroarchParser.mly"
                                    (USpecLang.FOLName (_2, _4))
# 456 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'params) in
    Obj.repr(
# 74 "MicroarchParser.mly"
                           (USpecLang.FOLExpandMacro (_2, _3))
# 464 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 75 "MicroarchParser.mly"
                    (USpecLang.FOLExpandMacro (_2, []))
# 471 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 76 "MicroarchParser.mly"
                          (_2)
# 478 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'predicate) in
    Obj.repr(
# 77 "MicroarchParser.mly"
              (USpecLang.FOLPredicate _1)
# 485 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 78 "MicroarchParser.mly"
                (USpecLang.FOLNot _2)
# 492 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 79 "MicroarchParser.mly"
                        (USpecLang.FOLAnd (_1, _3))
# 500 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 80 "MicroarchParser.mly"
                       (USpecLang.FOLOr (_1, _3))
# 508 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 81 "MicroarchParser.mly"
                            (USpecLang.fOLImplies _1 _3)
# 516 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 82 "MicroarchParser.mly"
                        (USpecLang.fOLIff _1 _3)
# 524 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'quantifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 83 "MicroarchParser.mly"
                                    (USpecLang.FOLExists (_2, _4))
# 532 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'quantifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 84 "MicroarchParser.mly"
                                    (USpecLang.FOLForAll (_2, _4))
# 540 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'qstring) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 86 "MicroarchParser.mly"
    (
      USpecLang.FOLExists (USpecLang.microopQuantifier(_5),
        USpecLang.FOLAnd
          (USpecLang.FOLPredicate(USpecLang.PredHasGlobalID(_3, _5)), _7))
    )
# 553 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 93 "MicroarchParser.mly"
                    (USpecLang.microopQuantifier(_2))
# 560 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 94 "MicroarchParser.mly"
                 (USpecLang.coreQuantifier(_2))
# 567 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 95 "MicroarchParser.mly"
                   (USpecLang.threadQuantifier(_2))
# 574 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "MicroarchParser.mly"
             (USpecLang.Accessed)
# 580 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "MicroarchParser.mly"
                (USpecLang.NotAccessed)
# 586 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "MicroarchParser.mly"
                     (USpecLang.AccessedDontCare)
# 592 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "MicroarchParser.mly"
          (USpecLang.Dirty)
# 598 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 104 "MicroarchParser.mly"
             (USpecLang.NotDirty)
# 604 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 105 "MicroarchParser.mly"
                  (USpecLang.DirtyDontCare)
# 610 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 108 "MicroarchParser.mly"
                            (USpecLang.fOLLookupPredicate_IIIIS _1 _2 _3 _4 _5 _6)
# 622 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 109 "MicroarchParser.mly"
                    (USpecLang.fOLLookupPredicate_SSS _1 _2 _3 _4)
# 632 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 110 "MicroarchParser.mly"
                (USpecLang.fOLLookupPredicate_SS _1 _2 _3)
# 641 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'accessedStatus) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'dirtyStatus) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 112 "MicroarchParser.mly"
    (USpecLang.fOLLookupPredicate_ADSS _1 _2 _3 _4 _5)
# 652 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'accessedStatus) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'dirtyStatus) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 114 "MicroarchParser.mly"
    (USpecLang.fOLLookupPredicate_ADS _1 _2 _3 _4)
# 662 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 115 "MicroarchParser.mly"
                (USpecLang.fOLLookupPredicate_IS _1 _2 _3)
# 671 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 116 "MicroarchParser.mly"
            (USpecLang.fOLLookupPredicate_S _1 _2)
# 679 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 117 "MicroarchParser.mly"
             (USpecLang.fOLLookupPredicate_E _1 _2)
# 687 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'edgelist) in
    Obj.repr(
# 118 "MicroarchParser.mly"
                 (USpecLang.fOLLookupPredicate_lE _1 _2)
# 695 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 119 "MicroarchParser.mly"
             (USpecLang.fOLLookupPredicate_N _1 _2)
# 703 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'nodelist) in
    Obj.repr(
# 120 "MicroarchParser.mly"
                 (USpecLang.fOLLookupPredicate_lN _1 _2)
# 711 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    Obj.repr(
# 121 "MicroarchParser.mly"
                               (USpecLang.fOLLookupPredicate_custom_S _3 _4)
# 719 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'edges) in
    Obj.repr(
# 124 "MicroarchParser.mly"
                          (_2)
# 726 "MicroarchParser.ml"
               : 'edgelist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'edges) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 127 "MicroarchParser.mly"
                         (_1 @ [_3])
# 734 "MicroarchParser.ml"
               : 'edges))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 128 "MicroarchParser.mly"
         ([_1])
# 741 "MicroarchParser.ml"
               : 'edges))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'node) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'node) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 132 "MicroarchParser.mly"
    (
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      USpecLang.Pair(USpecLang.Pair(USpecLang.Pair (_2, _4), linenum ^ ":" ^ _6),
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
    )
# 768 "MicroarchParser.ml"
               : 'edge))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'node) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : 'node) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 152 "MicroarchParser.mly"
    (
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      USpecLang.Pair(USpecLang.Pair(USpecLang.Pair (_2, _4),
        linenum ^ ":" ^ _6), _8)
    )
# 783 "MicroarchParser.ml"
               : 'edge))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'nodes) in
    Obj.repr(
# 160 "MicroarchParser.mly"
                          (_2)
# 790 "MicroarchParser.ml"
               : 'nodelist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'nodes) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 163 "MicroarchParser.mly"
                         (_1 @ [_3])
# 798 "MicroarchParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 164 "MicroarchParser.mly"
         ([_1])
# 805 "MicroarchParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'str) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'string_or_int) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'string_or_int) in
    Obj.repr(
# 168 "MicroarchParser.mly"
    (USpecLang.Pair (_2, USpecLang.Pair (_5, _7)))
# 814 "MicroarchParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'string_or_int) in
    Obj.repr(
# 170 "MicroarchParser.mly"
    (USpecLang.Pair (_2, USpecLang.Pair (USpecLang.SoICoreID _2, _4)))
# 822 "MicroarchParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'string_or_int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 173 "MicroarchParser.mly"
                                     (USpecLang.SoISum (_1, _3))
# 830 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 174 "MicroarchParser.mly"
        (USpecLang.SoIString _1)
# 837 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 175 "MicroarchParser.mly"
        (USpecLang.SoIInt _1)
# 844 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 176 "MicroarchParser.mly"
               (USpecLang.SoICoreID _2)
# 851 "MicroarchParser.ml"
               : 'string_or_int))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : USpecLang.microarchitecturalComponent)
