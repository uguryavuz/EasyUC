# 12 "dlLexer.mll"
 
  open DlParser
  open EcUtils
  module L  = EcLocation
  exception LexicalError of L.t option * string

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let _keywords = [                     
    "direct"        , DIRIO      ;
    "adversarial"   , ADVIO      ;
    "in"              , IN         ;
    "out"             , OUT        ;
    "message"         , MESSAGE    ;
    "functionality"   , FUNCT      ;
    "implements"      , IMPLEM     ;
    "party"           , PARTY      ;
    "serves"          , SERVES     ;
    "uses"            , USES       ;
    "initial"         , INITIAL    ;
    "state"           , STATE      ;
    "match"           , MATCH      ;
    "othermsg"        , OTHERMSG   ;
    "fail"            , FAIL       ;
    "send"            , SEND       ;
    "and"             , ANDTXT     ;
    "transition"      , TRANSITION ;
    "requires"        , REQUIRES   ;
    "var"             , VAR        ;
    "subfun"          , SUBFUN     ;
    "if"              , IF         ;
    "elif"            , ELIF       ;
    "else"            , ELSE       ;
    "simulator"       , SIM        ;
    "simulates"       , SIMS       ;
    "encode"          , ENCODE     ;
    "decode"          , DECODE     ;
    "as"              , AS         ;
    "with"            , WITH       ;
    "ok"              , OK         ;
    "error"           , ERROR      ;
    "end"             , END        ;
  ]

  let _operators = [
    ("^"   , HAT );
    ("/\\" , AND );
    ("\\/" , OR  );
    ("="   , EQ  );
    ("*"   , STAR);
  ]

  let operators =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _operators; table

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table

  let lex_operators (op : string) =
    try  Hashtbl.find operators op
    with Not_found -> ROP4 op
	


# 73 "dlLexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\233\255\234\255\235\255\000\000\239\255\241\255\242\255\
    \243\255\000\000\245\255\246\255\247\255\248\255\249\255\250\255\
    \001\000\061\000\160\000\002\000\255\255\244\000\046\001\252\255\
    \240\255\237\255\238\255\159\000\179\000\251\255\252\255\253\255\
    \006\000\008\000\255\255\254\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\255\255\022\000\255\255\255\255\255\255\
    \255\255\011\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \004\000\019\000\002\000\001\000\255\255\002\000\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\255\255\255\255\255\255\
    \004\000\004\000\255\255\255\255";
  Lexing.lex_default =
   "\001\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\255\255\255\255\255\255\000\000\255\255\255\255\000\000\
    \000\000\000\000\000\000\255\255\029\000\000\000\000\000\000\000\
    \255\255\255\255\000\000\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\019\000\020\000\019\000\000\000\019\000\000\000\019\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \019\000\005\000\019\000\000\000\026\000\000\000\000\000\000\000\
    \016\000\015\000\003\000\023\000\012\000\025\000\008\000\003\000\
    \035\000\034\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\011\000\010\000\004\000\009\000\024\000\000\000\
    \006\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\000\000\003\000\000\000\003\000\017\000\
    \000\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\014\000\007\000\013\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \000\000\000\000\000\000\000\000\022\000\000\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \000\000\000\000\000\000\000\000\000\000\031\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\018\000\
    \000\000\027\000\000\000\000\000\000\000\000\000\027\000\000\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\000\000\032\000\027\000\033\000\000\000\000\000\
    \000\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\027\000\000\000\027\000\000\000\018\000\
    \002\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\021\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\000\000\
    \000\000\000\000\000\000\021\000\000\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\000\000\000\000\000\000\000\000\022\000\000\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\030\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\019\000\255\255\000\000\255\255\019\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\019\000\255\255\004\000\255\255\255\255\255\255\
    \000\000\000\000\000\000\016\000\000\000\004\000\000\000\000\000\
    \032\000\033\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\000\000\000\000\000\000\009\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\255\255\000\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \255\255\255\255\255\255\255\255\017\000\255\255\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
    \255\255\255\255\255\255\255\255\255\255\028\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\018\000\
    \255\255\027\000\255\255\255\255\255\255\255\255\027\000\255\255\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\255\255\028\000\027\000\028\000\255\255\255\255\
    \255\255\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\027\000\255\255\027\000\255\255\018\000\
    \000\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
    \018\000\018\000\018\000\021\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\255\255\
    \255\255\255\255\255\255\021\000\255\255\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\021\000\021\000\021\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\255\255\255\255\255\255\255\255\022\000\255\255\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\028\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec read lexbuf =
   __ocaml_lex_read_rec lexbuf 0
and __ocaml_lex_read_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 117 "dlLexer.mll"
                 ( Lexing.new_line lexbuf; read lexbuf )
# 256 "dlLexer.ml"

  | 1 ->
# 118 "dlLexer.mll"
                 ( read lexbuf )
# 261 "dlLexer.ml"

  | 2 ->
let
# 119 "dlLexer.mll"
             id
# 267 "dlLexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 119 "dlLexer.mll"
                 ( try Hashtbl.find keywords id with Not_found -> ID (id) )
# 271 "dlLexer.ml"

  | 3 ->
# 120 "dlLexer.mll"
         ( comment lexbuf; read lexbuf )
# 276 "dlLexer.ml"

  | 4 ->
# 122 "dlLexer.mll"
          ( LPAREN     )
# 281 "dlLexer.ml"

  | 5 ->
# 123 "dlLexer.mll"
          ( RPAREN     )
# 286 "dlLexer.ml"

  | 6 ->
# 124 "dlLexer.mll"
          ( LBRACE     )
# 291 "dlLexer.ml"

  | 7 ->
# 125 "dlLexer.mll"
          ( RBRACE     )
# 296 "dlLexer.ml"

  | 8 ->
# 126 "dlLexer.mll"
          ( COMMA      )
# 301 "dlLexer.ml"

  | 9 ->
# 127 "dlLexer.mll"
          ( COLON      )
# 306 "dlLexer.ml"

  | 10 ->
# 128 "dlLexer.mll"
          ( SEMICOLON  )
# 311 "dlLexer.ml"

  | 11 ->
# 129 "dlLexer.mll"
          ( EQ         )
# 316 "dlLexer.ml"

  | 12 ->
# 130 "dlLexer.mll"
          ( DOT        )
# 321 "dlLexer.ml"

  | 13 ->
# 131 "dlLexer.mll"
          ( PIPE       )
# 326 "dlLexer.ml"

  | 14 ->
# 132 "dlLexer.mll"
          ( AT         )
# 331 "dlLexer.ml"

  | 15 ->
# 133 "dlLexer.mll"
          ( ARROW      )
# 336 "dlLexer.ml"

  | 16 ->
# 134 "dlLexer.mll"
          ( NOT        )
# 341 "dlLexer.ml"

  | 17 ->
# 135 "dlLexer.mll"
          ( ASGSAMPLE  )
# 346 "dlLexer.ml"

  | 18 ->
# 136 "dlLexer.mll"
          ( ASGVAL     )
# 351 "dlLexer.ml"

  | 19 ->
# 137 "dlLexer.mll"
          ( UNDERSCORE )
# 356 "dlLexer.ml"

  | 20 ->
let
# 139 "dlLexer.mll"
              op
# 362 "dlLexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 139 "dlLexer.mll"
                 (
      let op = operator (Buffer.from_char op) lexbuf in
      lex_operators (Buffer.contents op)
    )
# 369 "dlLexer.ml"

  | 21 ->
# 144 "dlLexer.mll"
          ( EOF        )
# 374 "dlLexer.ml"

  | 22 ->
# 145 "dlLexer.mll"
          ( lex_error lexbuf "invalid character")
# 379 "dlLexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_read_rec lexbuf __ocaml_lex_state

and operator buf lexbuf =
   __ocaml_lex_operator_rec buf lexbuf 27
and __ocaml_lex_operator_rec buf lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 148 "dlLexer.mll"
               x
# 392 "dlLexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 148 "dlLexer.mll"
                 ( Buffer.add_string buf x; buf )
# 396 "dlLexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_operator_rec buf lexbuf __ocaml_lex_state

and comment lexbuf =
   __ocaml_lex_comment_rec lexbuf 28
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 151 "dlLexer.mll"
                ( () )
# 408 "dlLexer.ml"

  | 1 ->
# 152 "dlLexer.mll"
                ( comment lexbuf; comment lexbuf )
# 413 "dlLexer.ml"

  | 2 ->
# 153 "dlLexer.mll"
                ( Lexing.new_line lexbuf; comment lexbuf )
# 418 "dlLexer.ml"

  | 3 ->
# 154 "dlLexer.mll"
                ( unterminated_comment () )
# 423 "dlLexer.ml"

  | 4 ->
# 155 "dlLexer.mll"
                ( comment lexbuf )
# 428 "dlLexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;
