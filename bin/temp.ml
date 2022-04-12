open Lib
open Lib.Formulas
open Lib.Axioms

(* open Uspec.Translate *)
(* open Uspec.MicroarchParser *)
(* open Uspec.MicroarchLexer *)
(* open Lexing *)

(* open Unix *)
open List

(* let getCore = function
  | Program.Core(1) -> "core1"
  | Program.Core(2) -> "core2"
  | _ -> "other" *)

let simple_print sp str = print_string ((if (sp > 0) then " " else "")^str)
let print_axiomatic_formula sp fml = 
  let str = Axioms.ax_term_to_str fml in
  print_string ((if (sp > 0) then " " else "")^str)

let formula_one = Formulas.Forall("a", Formulas.And(Atom("a"), Atom("b")))

let axstr : string = "Axiom \"Writes\":
  OnCore c i =>
  IsAnyWrite i =>
  AddEdges [
    ((i, Fetch          ), (i, Decode         ), \"path\");
    ((i, Decode         ), (i, Execute        ), \"path\");
    ((i, Execute        ), (i, MemoryStage    ), \"path\");
    ((i, MemoryStage    ), (i, Writeback      ), \"path\");
    ((i, Writeback      ), (i, StoreBuffer    ), \"path\");
    ((i, StoreBuffer    ), (i, L1ViCLCreate   ), \"path\");
    ((i, L1ViCLCreate   ), (i, L1ViCLDowngrade), \"path\");
    ((i, L1ViCLDowngrade), (i, L1ViCLExpire   ), \"path\")
  ]."

let formula_0 =
  And(
  And(Imp(And(Atom(PredicateTwo("sameInstr", "ev1", "ev2")),
          And(Atom(PredicateOne("isFetch", "ev1")),
              Atom(PredicateOne("isDecode", "ev2")))),
          Atom(HB("ev1", "ev2"))),
      Imp(And(Atom(PredicateTwo("sameInstr", "ev1", "ev2")),
          And(Atom(PredicateOne("isDecode", "ev1")),
              Atom(PredicateOne("isExecute", "ev2")))),
          Atom(HB("ev1", "ev2")))),
      Imp(And(Atom(PredicateTwo("notEqual", "ev1", "ev2")),
          And(Atom(PredicateTwo("po", "ev1", "ev2")),
          And(Atom(PredicateOne("isFetch", "ev1")),
              Atom(PredicateOne("isFetch", "ev2"))))),
          Atom(HB("ev1", "ev2"))))

let cxt_2 evstr =
match evstr with
| "ev1" -> Axioms.His
| "ev2" -> Axioms.Fut
| _ -> Axioms.His

let formulax_1 = 
  Imp(And(Atom(PredicateTwo("sameInstr", "ev1", "ev3")), 
      And(Atom(PredicateTwo("sameInstr", "ev2", "ev4")),
      And(Atom(PredicateOne("isFetch", "ev1")),
      And(Atom(PredicateOne("isFetch", "ev2")),
      And(Atom(PredicateOne("isExecute", "ev3")),
          Atom(PredicateOne("isExecute", "ev4"))))))),
  Formulas.Imp(Atom(HB("ev1", "ev2")), Atom(HB("ev3", "ev4"))))

let cxt_1 evstr = 
  match evstr with
  | "ev1" -> Axioms.His
  | "ev2" -> Axioms.Sched
  | "ev3" -> Axioms.Fut
  | _ -> Axioms.Fut

let analyse_single_context_clean formula_ (cxt_ : Axioms.context) =
  (* let cxt = {k = num_ev, cxt_map = cxt_map_} in *)
  print_endline (Axioms.get_cxt cxt_);
  let prev_flag = (Axioms.prev_cmt formula_ cxt_.cxt_map)
  and can_eval_fml_ = (Axioms.can_eval formula_ cxt_.cxt_map) in
  if (fst can_eval_fml_ == False) then
    if (not prev_flag) then
      failwith "Incomplete information: cannot work with these axioms!"
    else
      (print_endline (string_of_bool prev_flag);
      print_endline "(constant true)";
      print_endline "(constant true)";)
  else 
    (print_endline (string_of_bool prev_flag);
    (* print_endline "(constant true)"; *)
    print_endline (Formulas.get_simulax_guard Axioms.ax_term_to_str 
                  (Formulas.simplify (fst can_eval_fml_)));
    print_endline ((Formulas.get_simulax_guard Axioms.ax_term_to_str 
                (Formulas.simplify (snd can_eval_fml_))));)

let analyse_single_context formula_ (cxt_ : Axioms.context) =
  (* let cxt = {k = num_ev, cxt_map = cxt_map_} in *)
  print_endline "";
  print_endline ";; -- context --";
  print_endline (Axioms.get_cxt cxt_);
  print_endline ";; -- is prev --";
  let prev_flag = (Axioms.prev_cmt formula_ cxt_.cxt_map) in
  print_endline (string_of_bool prev_flag);
  if (prev_flag) then
    print_endline ";; all good!"
  else 
    (print_endline ";; -- can eval -";
    print_endline ("(canEval "^(Formulas.get_simulax_guard Axioms.ax_term_to_str (Formulas.simplify (fst (Axioms.can_eval formula_ cxt_.cxt_map))))^")");
    print_endline ";; -- eval --";
    print_endline ("(eval "^(Formulas.get_simulax_guard Axioms.ax_term_to_str (Formulas.simplify (snd (Axioms.can_eval formula_ cxt_.cxt_map))))^")");)
  
let all_contexts formula_ (num_ev : int) =
  let rec context_generator_helper num_ev_id cxt_map_ =
    if (num_ev_id < 1) then 
      let cxt_ : Axioms.context = {k = num_ev; cxt_map = cxt_map_} in
        analyse_single_context_clean formula_ cxt_;
    else 
      let dfun (newanno : Axioms.annotation) (ev : string) : Axioms.annotation =
        if (ev = "ev"^(string_of_int num_ev_id)) then newanno
        else (cxt_map_ ev) in 
      context_generator_helper (num_ev_id - 1) (dfun Axioms.His);
      context_generator_helper (num_ev_id - 1) (dfun Axioms.Sched);
      context_generator_helper (num_ev_id - 1) (dfun Axioms.Fut);
  and plain_map ev_ =
    match ev_ with
    | _ -> Axioms.His
  (* and print_single_context cxt_ =
    print_endline ";; -- context --";
    (* print_endline (string_of_annotation (cxt_.cxt_map "ev1")); *)
    print_endline (Axioms.get_cxt cxt_);  *)
  in context_generator_helper num_ev plain_map;;



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
  let archfile = Sys.argv.(1) in
  let parsedOp = (parse_uarch archfile 0) in
  (* print_int (length (parse_uarch "uarchs/temp.uarch" 1));
  print_int (length (List.nth parsedOp 1)); *)
  print_string (Uspec.Translate.convertToLisp "temp" (List.nth parsedOp 0));
  (* all_contexts formula_0 2; *)

  (* let retstring = (getCore (Program.Core 1)) in   *)
  (* print_endline (String.concat "" ["Hello, world!" ; retstring]);
  Formulas.print_formula simple_print formula_one;
  print_newline ();
  print_string (string_of_bool (Formulas.check_skolem_prenex formula_one));
  print_newline ();
  Formulas.print_formula print_axiomatic_formula formulax_1;
  print_newline (); *)
  (* Axioms.print_set (preds_in formulax_1); *)
  (* print_endline ";; -- context --";
  let cxt1 = {k = 2; cxt_map = cxt_2} in
  print_endline (Axioms.get_cxt cxt1);
  print_endline ";; -- is prev --";
  print_endline (string_of_bool (Axioms.prev formula_0 cxt_2 Commit));
  print_endline ";; -- can eval --";
  print_endline ("(canEval "^(Formulas.get_simulax_guard Axioms.ax_term_to_str (Formulas.simplify (fst (Axioms.can_eval formula_0 cxt_2))))^")");
  print_newline ();
  print_endline ";; -- eval --";
  print_endline ("(eval "^(Formulas.get_simulax_guard Axioms.ax_term_to_str (Formulas.simplify (snd (Axioms.can_eval formula_0 cxt_2))))^")"); *)