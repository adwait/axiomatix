open List

let rec n_copies n x =
  if n > 0 then (x :: n_copies (n-1) x) else [x]

  let parse_uarch filename num_cores =
  let in_channel = open_in filename in
  (* let channel = Unix.in_channel_of_descr file_descr in *)
  let lexbuf = Lexing.from_channel in_channel in
  try
    let pipeline = Uspec.MicroarchParser.main Uspec.MicroarchLexer.token lexbuf in
    n_copies num_cores pipeline
  with _ ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let token = Lexing.lexeme lexbuf in
      Printf.printf "Microarchitecture parsing error: line %d, offset %d, token %s\n"
        line offset token;
      raise (Failure "Parsing microarchitecture")
    end

let () = 
  let archfile = Sys.argv.(1) and
  outfile = open_out Sys.argv.(2) and
  uarchname = Sys.argv.(3) in
  let parsedOp = (parse_uarch archfile 0) in
  Printf.fprintf outfile "%s" (Uspec.Translate.convertToLisp uarchname (List.nth parsedOp 0));
