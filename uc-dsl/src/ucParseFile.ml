(* UcParseFile module *)

(* parse a DSL Specification *)

open EcLocation
open UcMessage
open UcLexer
module L = Lexing
open UcSpec

let lexbuf_from_channel file ch =
  let lexbuf = Lexing.from_channel ch in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = file;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

type file_or_id =
  | FOID_File of string  (* file name, interpreted relative to working
                            directory, if not fully qualified *)
  | FOID_Id   of id      (* root name of .uc file, matching ident from
                            lexer (and so without ".uc" and without "/"s *)

let foid_to_str foid =
  match foid with
  | FOID_File s  -> s
  | FOID_Id   id -> unloc id

let parse_file_or_id foid =
  let inc_dirs = UcState.get_include_dirs () in
  let (ch, file) =
    match foid with
    | FOID_File file ->
        (try open_in file, file with
         | Sys_error _ ->
             non_loc_error_message
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ open@ file:@ %s@]" file))
    | FOID_Id id     ->
        let uid = unloc id in
        (match UcUtils.find_file uid ".uc" inc_dirs with
         | None           ->
             error_message (loc id)
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ find@ .uc@ file:@ %s@]" uid)
         | Some qual_file ->
             (try open_in qual_file, qual_file with
              | Sys_error _ ->
                  error_message (loc id)
                  (fun ppf ->
                     Format.fprintf ppf
                     "@[unable@ to@ open@ file:@ %s@]" qual_file))) in
  let lexbuf = lexbuf_from_channel file ch in
  try (let res = (UcParser.spec read lexbuf, file) in
       close_in ch; res) with
  | UcParser.Error ->
      (error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))
