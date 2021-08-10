(* type truth_ops = DAnd | DOr | DNot | DIff | DImplies
type truth_values = DTrue | DFalse | DEval | DUndet *)
(* type truth_locations = DPrev | DEnc | DCurr *)
(* type truths =
  | DEnc 
  | DPrev
  | DCurr 
  | DUndet 
  | DAnd of truths * truths
  | DOr of truths * truths
  | DIff of truths * truths
  | DImplies of truths * truths
  | DNot of truths *)



(* let simplification_cmt fml cxt =
  let rec simplification_rec fml cxt =
    match fml with
    (* base cases *)
    | False -> Anno(DFalse, False)
    | True -> Anno(DTrue, True)
    | Atom(pred) -> Anno(simpl_atom pred cxt, Atom(pred))
    (* inductive cases *)
    | And(x, y) -> Anno(simpl_and 
      (simplification_rec x cxt) (simplification_rec y cxt) cxt, 
      And(x, y))
    | _ -> failwith "simplification_rec: nonmatch" 
  and simpl_atom fml cxt =
    match fml with
    | HB(ev1, ev2) -> 
      if (cxt ev1 == His && cxt ev2 == His) then DPrev
      else if (cxt ev1 == His && cxt ev2 != His) then DTrue
      else if (cxt ev1 != His && cxt ev2 == His) then DFalse
      else if (cxt ev1 != Fut && cxt ev2 == Fut) then DTrue
      else if (cxt ev1 == Fut && cxt ev2 != Fut) then DFalse
      else if (cxt ev1 == Fut && cxt ev2 == Fut) then DCurr
      else if (cxt ev1 == Sched && cxt ev2 == Sched) then DEnc
      else failwith "simpl_atom: nonmatch for HB"
    (* assuming a constant predicate *)
    | PredicateOne(ev1) -> 
      if (cxt ev1 == His) then DPrev
      else if (cxt ev1 == Sched) then DEnc
      else if (cxt ev1 == Fut) then DEnc
      (* if (cxt ev == His) then DPrev
      else if (cxt ev == Sched) then DEnc
      else if (cxt ev == Fut) then DCurr *)
      else failwith "simpl_atom : nonmatch for PredicateOne"
    | PredicateTwo(ev1, ev2) -> 
      if (cxt ev1 == His && cxt ev2 == His) then DPrev
      else if (cxt ev1 == Sched) then DEnc
      else if (cxt ev1 == Fut) then DEnc
      (* if (cxt ev == His) then DPrev
      else if (cxt ev == Sched) then DEnc
      else if (cxt ev == Fut) then DCurr *)
      else failwith "simpl_atom : nonmatch for PredicateTwo"
    and simpl_and x y cxt = 
    match x, y with
    | Anno(xTrue, _), Anno(yTrue, _) -> 
      | Anno(DTrue, _) -> DTrue
  in
  simplification_rec fml cxt *)
