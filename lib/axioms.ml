(* ========================================================================= *)
(* Axiomatic semantics.                                                      *)
(* ========================================================================= *)

(* open Event *)
open Formulas
module SS = Set.Make(String)

(* Events in the abstract system *)
type event_variable = Event of string
let event_name (Event ev) = ev

(* type predicate = 
  | SameInstr
  | SameCore
  | SameValue
  | SameAddr
  | SameLabel
  | NotEqual
  | IsWrite
  | IsRead
  | IsFetch
  | IsDecode
  | IsExecute
  | PO *)


(* Regions in the abstract system *)
type annotation = His | Sched | Fut
let string_of_annotation tr =
  match tr with
  | His -> "history"
  | Sched -> "scheduled" 
  | Fut -> "future" 



type context = {k : int; cxt_map : string ->  annotation}
let get_cxt (cxt : context) =
  let rec get_cxt_rec i =
    (if i > 1 then (get_cxt_rec (i-1))^" " else "")^
    string_of_annotation (cxt.cxt_map ("ev"^(string_of_int i))) in
  get_cxt_rec cxt.k



(* Transitions in the abstract system *)
type transition = 
  | Commit
  | Schedule
let string_of_transition tr =
  match tr with
  | Commit -> "commit"
  | Schedule -> "schedule" 

(* Atomic terms *)
type axiomatic_term = 
  | HB of string * string
  | PredicateOne of string * string
  | PredicateTwo of string * string * string

(* Print atomic terms 
    supply as leaf-routine to formula printer*)
let ax_term_to_str term = 
  match term with
  | HB(ev1, ev2) -> "(predicate hb (event "^ev1^") (event "^ev2^"))"
  | PredicateOne(pname, ev1) -> "(predicate "^pname^" (event "^ev1^"))"
  | PredicateTwo(pname, ev1, ev2) -> "(predicate "^pname^" (event "^ev1^") (event "^ev2^"))"

let dand_semantics ce_x fx ce_y fy =
  match fx, fy with
  | Undet, Undet -> (False, Undet)
  | Undet, _ -> (And(ce_y, Not(fy)), False)
  | _, Undet -> (And(ce_x, Not(fx)), False)
  | _, _ ->  
    (
      Or(And(ce_x, ce_y), 
        Or(And(ce_x, Not(fx)), 
        And(ce_y, Not(fy)))), 
      And(And(ce_x, ce_y), And(fx, fy))
    )

let dor_semantics ce_x fx ce_y fy =
  match fx, fy with
  | Undet, Undet -> (False, Undet)
  | Undet, _ -> (And(ce_y, fy), True)
  | _, Undet -> (And(ce_x, fx), True)
  | _, _ ->  
    (
      Or(And(ce_x, ce_y), 
        Or(And(ce_x, fx), 
        And(ce_y, fy))), 
      Or(And(And(ce_x, ce_y), Or(fx, fy)),
        Not(And(ce_x, ce_y)))
    )

let dimp_semantics ce_x fx ce_y fy =
  match fx, fy with
  | Undet, Undet -> (False, Undet)
  | Undet, _ -> (And(ce_y, fy), True)
  | _, Undet -> (And(ce_x, Not(fx)), True)
  | _, _ ->  
    (
      Or(And(ce_x, ce_y), 
        Or(And(ce_x, Not(fx)), 
        And(ce_y, fy))), 
      Or(And(And(ce_x, ce_y), Imp(fx, fy)),
        And(Not(And(ce_x, ce_y)), True))
    ) 
    
let diff_semantics ce_x fx ce_y fy =
  match fx, fy with
  | Undet, _ -> (False, Undet)
  | _, Undet -> (False, Undet)
  | _, _ -> (And(ce_x, ce_y), Iff(fx, fy))    

let dnot_semantics ce_x fx =
  match fx with
  | Undet -> (False, Undet)
  | _ ->  (ce_x, Not(fx))    

let predicateTwoManager predname ev1 cxt1 ev2 cxt2 = 
  if (cxt1 == His && cxt2 == His) then (False, Undet)
  else if (cxt1 == Sched || cxt1 == Fut) && (cxt2 == Sched && cxt2 == Fut) 
    then (True, Atom(PredicateTwo(predname, ev1, ev2)))
  else match predname with
  | _ -> (True, Atom(PredicateTwo(predname, ev1, ev2)))

let prev fml cxt (tr : transition) : bool =
  let rec prev_rec fml cxt tr =
    match fml with
    | False -> true
    | True -> true
    | Atom(pred) -> 
      (if tr == Commit then (prev_cmt_atom pred) else (prev_sch_atom pred))
    | And(x, y) -> (prev_rec x cxt tr) && (prev_rec y cxt tr)
    | Or(x, y) -> (prev_rec x cxt tr) && (prev_rec y cxt tr)
    | Not(x) -> (prev_rec x cxt tr)
    | Iff(x, y) -> (prev_rec x cxt tr) && (prev_rec y cxt tr)
    | Imp(x, y) -> (prev_rec x cxt tr) && (prev_rec y cxt tr)
    | _ -> failwith "prev_rec: nonmatch" 
  and prev_cmt_atom pred = 
    match pred with
    | HB(ev1, ev2) -> 
      if cxt ev1 == His || cxt ev2 == His then true
      else if cxt ev1 == Sched || cxt ev2 == Sched then true
      else false
    | _ -> true
  and prev_sch_atom pred = 
    match pred with  
    | HB(ev1, ev2) -> 
      if (cxt ev1 == His || cxt ev2 == His) then true 
      else false
    | _ -> true in
  prev_rec fml cxt tr

let prev_cmt fml cxt = (prev fml cxt Commit)
let prev_sch fml cxt = (prev fml cxt Schedule)

(* Returns:
    - precondition on expression evaluation : formula
    - simplified expression : formula *)
let can_eval fml cxt =
  let rec can_eval_rec fml cxt =
    match fml with
    | False -> (True, True)
    | True -> (True, False)
    | Atom(pred) -> (can_eval_atom pred)
    | And(x, y) -> and_combinator (can_eval_rec x cxt) (can_eval_rec y cxt)
    | Or(x, y) -> or_combinator (can_eval_rec x cxt) (can_eval_rec y cxt)
    | Not(x) -> not_combinator (can_eval_rec x cxt)
    | Iff(x, y) -> iff_combinator (can_eval_rec x cxt) (can_eval_rec y cxt)
    | Imp(x, y) -> imp_combinator (can_eval_rec x cxt) (can_eval_rec y cxt)
    | _ -> failwith "can_eval_rec: nonmatch" 
  and can_eval_atom pred = 
    match pred with
    | HB(ev1, ev2) -> 
      if cxt ev1 == His && cxt ev2 != His then (True, True)
      else if cxt ev1 != His && cxt ev2 == His then (True, False)
      else if cxt ev1 == His && cxt ev2 == His then (False, Undet)
      else if cxt ev1 == Sched && cxt ev2 == Fut then (True, True)
      else if cxt ev1 == Sched && cxt ev2 == Sched then (True, Atom(pred))
      else if cxt ev1 == Fut && cxt ev2 == Sched then (True, False)
      else if cxt ev1 == Fut && cxt ev2 == Fut then (True, Atom(pred))
      else failwith "can_eval_atom: HB nonmatch"
    | PredicateOne(_, ev) -> 
      if cxt ev == His then (False, Undet)
      else (True, Atom(pred))
      (* if cxt ev1 == His then (False, Undet)
      else if cxt ev1 == Sched then (True, Atom(pred))
      else if cxt ev1 == Fut then (True, Atom(pred)) *)
      (* else failwith "can_eval_atom: PredicateOne nonmatch" *)
    | PredicateTwo(predname, ev1, ev2) -> 
      if cxt ev1 == His && cxt ev2 == His then (False, Undet)
      else if (cxt ev1 == Fut || cxt ev1 == Sched)
        && (cxt ev2 == Fut || cxt ev2 == Sched) then (True, Atom(pred))
      else predicateTwoManager predname ev1 (cxt ev1) ev2 (cxt ev2)
      (* else failwith "can_eval_predicateTwo: non match" *)
      (* if cxt ev1 == His || cxt ev2 == His then (False, Undet)
      else if (cxt ev1 == Sched || cxt ev1 == Fut) && (cxt ev2 == Sched || cxt ev2 == Fut) 
        then (True, Atom(pred))
      else failwith "can_eval_atom: PredicateOne nonmatch" *)
    (* | _ -> failwith "can_eval_atom: nonmatch" *)
  and and_combinator x y = 
    let ce_left = fst x and ce_right = fst y 
    and eval_left = snd x and eval_right = snd y in
    dand_semantics ce_left eval_left ce_right eval_right
  and or_combinator x y = 
    let ce_left = fst x and ce_right = fst y 
    and eval_left = snd x and eval_right = snd y in
    dor_semantics ce_left eval_left ce_right eval_right
  and iff_combinator x y = 
    let ce_left = fst x and ce_right = fst y 
    and eval_left = snd x and eval_right = snd y in
    diff_semantics ce_left eval_left ce_right eval_right
  and imp_combinator x y = 
    let ce_left = fst x and ce_right = fst y 
    and eval_left = snd x and eval_right = snd y in
    dimp_semantics ce_left eval_left ce_right eval_right
  and not_combinator x = 
    let ce_left = fst x and eval_left = snd x in
    dnot_semantics ce_left eval_left in
  can_eval_rec fml cxt



(* precondition on providing a judgement : formula *)
let allows_judgement fml cxt (tr : transition) = 
  if (prev fml cxt tr) then Formulas.True
  else fst (can_eval fml cxt)

let preds_in fml =
  let rec preds_in_fml_rec fml =
  match fml with
  | Undet -> SS.empty
  | False -> SS.empty
  | True -> SS.empty
  | Atom(pred) -> (
    match pred with
    | HB(_, _) -> SS.empty
    | PredicateOne(predname, _) -> SS.singleton predname
    | PredicateTwo(predname, _, _) -> SS.singleton predname )
  | And(x, y) -> SS.union (preds_in_fml_rec x) (preds_in_fml_rec y)
  | Or(x, y) -> SS.union (preds_in_fml_rec x) (preds_in_fml_rec y)
  | Not(x) -> (preds_in_fml_rec x)
  | Iff(x, y) -> SS.union (preds_in_fml_rec x) (preds_in_fml_rec y)
  | Imp(x, y) -> SS.union (preds_in_fml_rec x) (preds_in_fml_rec y)
  | _ -> failwith "can_eval_rec: nonmatch" in
  preds_in_fml_rec fml

let print_set s = SS.iter print_endline s

(* let get_terms_for fml cxt ev  =
  let rec get_terms_for_rec fml =
    match fml with
    | Undet | False | True -> []
    | Atom(pred) -> (
      match pred with
      | HB(ev1, ev2) -> 
      |
    ) *)