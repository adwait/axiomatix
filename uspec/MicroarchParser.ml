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

open Parsing;;
let _ = parse_error;;
# 2 "MicroarchParser.mly"
  open Lexing
# 50 "MicroarchParser.ml"
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
  285 (* LBRACKET *);
  286 (* RBRACKET *);
  287 (* ANYNAME *);
  288 (* WITH *);
  289 (* AS *);
    0 (* EOF *);
  290 (* PLUS *);
  291 (* COREID *);
  292 (* ACCESSED *);
  293 (* NOTACCESSED *);
  294 (* ACCESSEDDONTCARE *);
  295 (* DIRTY *);
  296 (* NOTDIRTY *);
  297 (* DIRTYDONTCARE *);
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
\013\000\013\000\018\000\021\000\021\000\017\000\017\000\020\000\
\022\000\022\000\019\000\019\000\011\000\011\000\011\000\011\000\
\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\001\000\001\000\001\000\004\000\005\000\
\006\000\005\000\002\000\001\000\002\000\001\000\003\000\002\000\
\001\000\005\000\003\000\002\000\003\000\001\000\002\000\003\000\
\003\000\003\000\003\000\004\000\004\000\007\000\002\000\002\000\
\002\000\001\000\001\000\001\000\001\000\001\000\001\000\006\000\
\004\000\003\000\005\000\004\000\003\000\002\000\002\000\002\000\
\002\000\002\000\003\000\003\000\001\000\007\000\009\000\003\000\
\003\000\001\000\009\000\005\000\003\000\001\000\001\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\065\000\000\000\003\000\
\004\000\005\000\006\000\000\000\000\000\000\000\000\000\001\000\
\002\000\017\000\016\000\000\000\012\000\000\000\000\000\000\000\
\000\000\015\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\022\000\011\000\000\000\007\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\023\000\000\000\000\000\
\000\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\034\000\035\000\036\000\000\000\000\000\047\000\048\000\
\049\000\050\000\000\000\008\000\063\000\000\000\000\000\000\000\
\062\000\031\000\032\000\033\000\000\000\000\000\021\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\045\000\000\000\
\000\000\000\000\053\000\058\000\000\000\000\000\000\000\037\000\
\038\000\039\000\000\000\009\000\064\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\051\000\
\000\000\056\000\041\000\000\000\061\000\018\000\000\000\000\000\
\000\000\000\000\000\000\000\000\052\000\057\000\043\000\000\000\
\040\000\000\000\060\000\000\000\000\000\000\000\000\000\000\000\
\000\000\054\000\000\000\000\000\059\000\055\000"

let yydgoto = "\002\000\
\006\000\007\000\008\000\009\000\010\000\011\000\013\000\033\000\
\023\000\071\000\072\000\034\000\035\000\044\000\062\000\099\000\
\063\000\064\000\065\000\066\000\093\000\094\000"

let yysindex = "\011\000\
\147\255\000\000\007\255\020\255\007\255\000\000\001\000\000\000\
\000\000\000\000\000\000\006\255\011\255\007\255\016\255\000\000\
\000\000\000\000\000\000\033\255\000\000\069\255\014\255\040\255\
\069\255\000\000\063\255\156\255\156\255\069\255\069\255\065\255\
\195\255\102\255\000\000\000\000\069\255\000\000\204\255\009\255\
\007\255\007\255\007\255\075\255\093\255\000\000\215\255\086\255\
\079\255\000\000\069\255\069\255\069\255\069\255\172\255\002\255\
\070\255\000\000\000\000\000\000\063\255\184\255\000\000\000\000\
\000\000\000\000\210\255\000\000\000\000\063\255\009\255\084\255\
\000\000\000\000\000\000\000\000\069\255\069\255\000\000\069\255\
\081\255\104\255\028\255\234\255\234\255\127\255\000\000\063\255\
\113\255\116\255\000\000\000\000\241\254\061\255\063\255\000\000\
\000\000\000\000\063\255\000\000\000\000\084\255\009\255\229\255\
\229\255\222\255\007\255\135\255\022\255\121\255\130\255\000\000\
\121\255\000\000\000\000\063\255\000\000\000\000\129\255\063\255\
\009\255\049\255\143\255\121\255\000\000\000\000\000\000\069\255\
\000\000\000\255\000\000\007\255\229\255\009\255\031\255\115\255\
\007\255\000\000\149\255\154\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\144\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\153\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\162\255\119\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\186\255\050\255\027\255\071\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\171\255\000\000\
\000\000\000\000\000\000\000\000\000\000\133\255\000\000\080\255\
\088\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\180\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\091\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\176\000\000\000\000\000\000\000\251\255\245\255\
\000\000\000\000\217\255\247\255\000\000\157\000\000\000\000\000\
\201\255\000\000\206\255\000\000\000\000\000\000"

let yytablesize = 263
let yytable = "\015\000\
\016\000\091\000\020\000\018\000\111\000\090\000\092\000\018\000\
\024\000\069\000\018\000\001\000\021\000\039\000\112\000\036\000\
\134\000\040\000\046\000\047\000\014\000\048\000\069\000\018\000\
\061\000\067\000\019\000\012\000\088\000\022\000\073\000\102\000\
\037\000\103\000\025\000\074\000\075\000\076\000\061\000\082\000\
\083\000\084\000\085\000\070\000\026\000\087\000\089\000\137\000\
\121\000\051\000\052\000\095\000\026\000\026\000\026\000\125\000\
\070\000\038\000\138\000\123\000\101\000\073\000\126\000\117\000\
\018\000\104\000\105\000\025\000\106\000\122\000\018\000\049\000\
\027\000\090\000\025\000\025\000\131\000\025\000\089\000\081\000\
\113\000\130\000\103\000\028\000\029\000\115\000\055\000\018\000\
\027\000\116\000\114\000\077\000\030\000\073\000\136\000\031\000\
\056\000\029\000\027\000\073\000\032\000\119\000\055\000\018\000\
\080\000\028\000\127\000\029\000\030\000\078\000\129\000\073\000\
\056\000\107\000\057\000\028\000\133\000\103\000\030\000\014\000\
\014\000\058\000\059\000\060\000\073\000\051\000\135\000\108\000\
\056\000\109\000\057\000\140\000\110\000\013\000\013\000\120\000\
\014\000\058\000\059\000\060\000\014\000\014\000\139\000\014\000\
\014\000\128\000\014\000\088\000\103\000\003\000\013\000\004\000\
\005\000\014\000\013\000\013\000\124\000\013\000\013\000\132\000\
\013\000\020\000\041\000\042\000\043\000\020\000\020\000\013\000\
\020\000\020\000\046\000\020\000\086\000\018\000\046\000\046\000\
\141\000\046\000\046\000\019\000\046\000\142\000\017\000\019\000\
\019\000\045\000\019\000\019\000\042\000\019\000\000\000\000\000\
\042\000\042\000\000\000\042\000\042\000\044\000\042\000\000\000\
\000\000\044\000\044\000\024\000\044\000\044\000\000\000\044\000\
\024\000\000\000\024\000\024\000\050\000\024\000\000\000\000\000\
\051\000\052\000\000\000\053\000\054\000\068\000\096\000\097\000\
\098\000\051\000\052\000\100\000\053\000\054\000\000\000\051\000\
\052\000\000\000\053\000\054\000\051\000\052\000\000\000\053\000\
\054\000\000\000\079\000\051\000\052\000\000\000\053\000\054\000\
\000\000\118\000\051\000\052\000\000\000\053\000\054\000\051\000\
\052\000\000\000\053\000\003\000\000\000\004\000\005\000"

let yycheck = "\005\000\
\000\000\057\000\012\000\002\001\020\001\056\000\057\000\002\001\
\014\000\001\001\002\001\001\000\002\001\025\000\030\001\002\001\
\017\001\027\000\030\000\031\000\001\001\031\000\001\001\002\001\
\034\000\037\000\021\001\021\001\027\001\019\001\040\000\071\000\
\019\001\034\001\019\001\041\000\042\000\043\000\048\000\051\000\
\052\000\053\000\054\000\035\001\018\001\055\000\056\000\017\001\
\027\001\022\001\023\001\061\000\026\001\021\001\028\001\111\000\
\035\001\018\001\028\001\110\000\070\000\071\000\113\000\103\000\
\002\001\077\000\078\000\018\001\080\000\109\000\002\001\007\001\
\004\001\124\000\025\001\026\001\028\001\028\001\088\000\001\001\
\020\001\121\000\034\001\015\001\016\001\095\000\001\001\002\001\
\018\001\099\000\030\001\017\001\024\001\103\000\134\000\027\001\
\027\001\018\001\028\001\109\000\032\001\107\000\001\001\002\001\
\019\001\018\001\116\000\028\001\018\001\017\001\120\000\121\000\
\027\001\033\001\029\001\028\001\128\000\034\001\028\001\001\001\
\002\001\036\001\037\001\038\001\134\000\022\001\132\000\001\001\
\027\001\017\001\029\001\137\000\017\001\001\001\002\001\001\001\
\018\001\036\001\037\001\038\001\022\001\023\001\028\001\025\001\
\026\001\017\001\028\001\027\001\034\001\003\001\018\001\005\001\
\006\001\035\001\022\001\023\001\027\001\025\001\026\001\017\001\
\028\001\018\001\007\001\008\001\009\001\022\001\023\001\035\001\
\025\001\026\001\018\001\028\001\001\001\002\001\022\001\023\001\
\028\001\025\001\026\001\018\001\028\001\028\001\007\000\022\001\
\023\001\029\000\025\001\026\001\018\001\028\001\255\255\255\255\
\022\001\023\001\255\255\025\001\026\001\018\001\028\001\255\255\
\255\255\022\001\023\001\018\001\025\001\026\001\255\255\028\001\
\023\001\255\255\025\001\026\001\018\001\028\001\255\255\255\255\
\022\001\023\001\255\255\025\001\026\001\018\001\039\001\040\001\
\041\001\022\001\023\001\018\001\025\001\026\001\255\255\022\001\
\023\001\255\255\025\001\026\001\022\001\023\001\255\255\025\001\
\026\001\255\255\028\001\022\001\023\001\255\255\025\001\026\001\
\255\255\028\001\022\001\023\001\255\255\025\001\026\001\022\001\
\023\001\255\255\025\001\003\001\255\255\005\001\006\001"

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
# 33 "MicroarchParser.mly"
                 (_1)
# 317 "MicroarchParser.ml"
               : USpecLang.microarchitecturalComponent))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statements) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 36 "MicroarchParser.mly"
                         (_1 @ [_2])
# 325 "MicroarchParser.ml"
               : 'statements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 37 "MicroarchParser.mly"
              ([_1])
# 332 "MicroarchParser.ml"
               : 'statements))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'axiom) in
    Obj.repr(
# 40 "MicroarchParser.mly"
          (USpecLang.FOLAxiom (_1))
# 339 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'macro) in
    Obj.repr(
# 41 "MicroarchParser.mly"
          (USpecLang.FOLMacroDefinition (_1))
# 346 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'contextterm) in
    Obj.repr(
# 42 "MicroarchParser.mly"
                (USpecLang.FOLContextTerm (_1))
# 353 "MicroarchParser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 45 "MicroarchParser.mly"
                               (USpecLang.StageNameTerm(_3, _2))
# 361 "MicroarchParser.ml"
               : 'contextterm))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 48 "MicroarchParser.mly"
                                     (USpecLang.FOLName (_2, _4))
# 369 "MicroarchParser.ml"
               : 'axiom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'qstring) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'args) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 52 "MicroarchParser.mly"
    (USpecLang.Pair(USpecLang.Pair(_2, _3), _5))
# 378 "MicroarchParser.ml"
               : 'macro))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 54 "MicroarchParser.mly"
    (USpecLang.Pair(USpecLang.Pair(_2, []), _4))
# 386 "MicroarchParser.ml"
               : 'macro))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 57 "MicroarchParser.mly"
                (_1 @ [_2])
# 394 "MicroarchParser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 58 "MicroarchParser.mly"
           ([_1])
# 401 "MicroarchParser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'params) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 61 "MicroarchParser.mly"
                         (_1 @ [_2])
# 409 "MicroarchParser.ml"
               : 'params))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 62 "MicroarchParser.mly"
                  ([_1])
# 416 "MicroarchParser.ml"
               : 'params))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    Obj.repr(
# 65 "MicroarchParser.mly"
                    (_2)
# 423 "MicroarchParser.ml"
               : 'qstring))
; (fun __caml_parser_env ->
    Obj.repr(
# 66 "MicroarchParser.mly"
                ("")
# 429 "MicroarchParser.ml"
               : 'qstring))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 69 "MicroarchParser.mly"
         (_1)
# 436 "MicroarchParser.ml"
               : 'str))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 72 "MicroarchParser.mly"
                                    (USpecLang.FOLName (_2, _4))
# 444 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'params) in
    Obj.repr(
# 73 "MicroarchParser.mly"
                           (USpecLang.FOLExpandMacro (_2, _3))
# 452 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 74 "MicroarchParser.mly"
                    (USpecLang.FOLExpandMacro (_2, []))
# 459 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 75 "MicroarchParser.mly"
                          (_2)
# 466 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'predicate) in
    Obj.repr(
# 76 "MicroarchParser.mly"
              (USpecLang.FOLPredicate _1)
# 473 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 77 "MicroarchParser.mly"
                (USpecLang.FOLNot _2)
# 480 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 78 "MicroarchParser.mly"
                        (USpecLang.FOLAnd (_1, _3))
# 488 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 79 "MicroarchParser.mly"
                       (USpecLang.FOLOr (_1, _3))
# 496 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 80 "MicroarchParser.mly"
                            (USpecLang.fOLImplies _1 _3)
# 504 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 81 "MicroarchParser.mly"
                        (USpecLang.fOLIff _1 _3)
# 512 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'quantifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 82 "MicroarchParser.mly"
                                    (USpecLang.FOLExists (_2, _4))
# 520 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'quantifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 83 "MicroarchParser.mly"
                                    (USpecLang.FOLForAll (_2, _4))
# 528 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'qstring) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 85 "MicroarchParser.mly"
    (
      USpecLang.FOLExists (USpecLang.microopQuantifier(_5),
        USpecLang.FOLAnd
          (USpecLang.FOLPredicate(USpecLang.PredHasGlobalID(_3, _5)), _7))
    )
# 541 "MicroarchParser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 92 "MicroarchParser.mly"
                    (USpecLang.microopQuantifier(_2))
# 548 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 93 "MicroarchParser.mly"
                 (USpecLang.coreQuantifier(_2))
# 555 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'qstring) in
    Obj.repr(
# 94 "MicroarchParser.mly"
                   (USpecLang.threadQuantifier(_2))
# 562 "MicroarchParser.ml"
               : 'quantifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "MicroarchParser.mly"
             (USpecLang.Accessed)
# 568 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "MicroarchParser.mly"
                (USpecLang.NotAccessed)
# 574 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "MicroarchParser.mly"
                     (USpecLang.AccessedDontCare)
# 580 "MicroarchParser.ml"
               : 'accessedStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 102 "MicroarchParser.mly"
          (USpecLang.Dirty)
# 586 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "MicroarchParser.mly"
             (USpecLang.NotDirty)
# 592 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    Obj.repr(
# 104 "MicroarchParser.mly"
                  (USpecLang.DirtyDontCare)
# 598 "MicroarchParser.ml"
               : 'dirtyStatus))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 107 "MicroarchParser.mly"
                            (USpecLang.fOLLookupPredicate_IIIIS _1 _2 _3 _4 _5 _6)
# 610 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 108 "MicroarchParser.mly"
                    (USpecLang.fOLLookupPredicate_SSS _1 _2 _3 _4)
# 620 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 109 "MicroarchParser.mly"
                (USpecLang.fOLLookupPredicate_SS _1 _2 _3)
# 629 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'accessedStatus) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'dirtyStatus) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 111 "MicroarchParser.mly"
    (USpecLang.fOLLookupPredicate_ADSS _1 _2 _3 _4 _5)
# 640 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'accessedStatus) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'dirtyStatus) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 113 "MicroarchParser.mly"
    (USpecLang.fOLLookupPredicate_ADS _1 _2 _3 _4)
# 650 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 114 "MicroarchParser.mly"
                (USpecLang.fOLLookupPredicate_IS _1 _2 _3)
# 659 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 115 "MicroarchParser.mly"
            (USpecLang.fOLLookupPredicate_S _1 _2)
# 667 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 116 "MicroarchParser.mly"
             (USpecLang.fOLLookupPredicate_E _1 _2)
# 675 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'edgelist) in
    Obj.repr(
# 117 "MicroarchParser.mly"
                 (USpecLang.fOLLookupPredicate_lE _1 _2)
# 683 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 118 "MicroarchParser.mly"
             (USpecLang.fOLLookupPredicate_N _1 _2)
# 691 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'str) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'nodelist) in
    Obj.repr(
# 119 "MicroarchParser.mly"
                 (USpecLang.fOLLookupPredicate_lN _1 _2)
# 699 "MicroarchParser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'edges) in
    Obj.repr(
# 122 "MicroarchParser.mly"
                          (_2)
# 706 "MicroarchParser.ml"
               : 'edgelist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'edges) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 125 "MicroarchParser.mly"
                         (_1 @ [_3])
# 714 "MicroarchParser.ml"
               : 'edges))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'edge) in
    Obj.repr(
# 126 "MicroarchParser.mly"
         ([_1])
# 721 "MicroarchParser.ml"
               : 'edges))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'node) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'node) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 130 "MicroarchParser.mly"
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
# 748 "MicroarchParser.ml"
               : 'edge))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'node) in
    let _4 = (Parsing.peek_val __caml_parser_env 5 : 'node) in
    let _6 = (Parsing.peek_val __caml_parser_env 3 : 'qstring) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'qstring) in
    Obj.repr(
# 150 "MicroarchParser.mly"
    (
      let startpos = Parsing.symbol_start_pos() in
      let linenum = string_of_int startpos.pos_lnum in
      USpecLang.Pair(USpecLang.Pair(USpecLang.Pair (_2, _4),
        linenum ^ ":" ^ _6), _8)
    )
# 763 "MicroarchParser.ml"
               : 'edge))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'nodes) in
    Obj.repr(
# 158 "MicroarchParser.mly"
                          (_2)
# 770 "MicroarchParser.ml"
               : 'nodelist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'nodes) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 161 "MicroarchParser.mly"
                         (_1 @ [_3])
# 778 "MicroarchParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'node) in
    Obj.repr(
# 162 "MicroarchParser.mly"
         ([_1])
# 785 "MicroarchParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'str) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'string_or_int) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'string_or_int) in
    Obj.repr(
# 166 "MicroarchParser.mly"
    (USpecLang.Pair (_2, USpecLang.Pair (_5, _7)))
# 794 "MicroarchParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'str) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'string_or_int) in
    Obj.repr(
# 168 "MicroarchParser.mly"
    (USpecLang.Pair (_2, USpecLang.Pair (USpecLang.SoICoreID _2, _4)))
# 802 "MicroarchParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'string_or_int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'string_or_int) in
    Obj.repr(
# 171 "MicroarchParser.mly"
                                     (USpecLang.SoISum (_1, _3))
# 810 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 172 "MicroarchParser.mly"
        (USpecLang.SoIString _1)
# 817 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 173 "MicroarchParser.mly"
        (USpecLang.SoIInt _1)
# 824 "MicroarchParser.ml"
               : 'string_or_int))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'str) in
    Obj.repr(
# 174 "MicroarchParser.mly"
               (USpecLang.SoICoreID _2)
# 831 "MicroarchParser.ml"
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
