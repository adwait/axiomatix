(* ========================================================================= *)
(* Polymorphic type of formulas.                                             *)
(* ========================================================================= *)

type ('a)formula = 
  | Undet
  | False
  | True
  | Atom of 'a
  | Not of ('a)formula
  | And of ('a)formula * ('a)formula
  | Or of ('a)formula * ('a)formula
  | Imp of ('a)formula * ('a)formula
  | Iff of ('a)formula * ('a)formula
  | Forall of string * ('a)formula
  | Exists of string * ('a)formula

(* ------------------------------------------------------------------------- *)
(* General printing                                                          *)
(* ------------------------------------------------------------------------- *)

let bracket _ n f x y =
  print_string "(";
  (* (if p then print_string "(" else ()); *)
  Format.open_box n; f x y; Format.close_box();
  print_string ")"
  (* (if p then print_string ")" else ()) *)

let rec strip_quant fm =
  match fm with
  | Forall(x,(Forall(_,_) as yp)) | Exists(x,(Exists(_,_) as yp)) ->
        let xs,q = strip_quant yp in x::xs,q
  |  Forall(x,p) | Exists(x,p) -> [x],p
  | _ -> [],fm

let print_formula pfn =
  let rec print_formula pr fm =
    match fm with
    | False -> print_string "false"
    | True -> print_string "true"
    | Atom(pargs) -> pfn pr pargs
    | Not(p) -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And(p, q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or(p, q) ->  bracket (pr > 6) 0 (print_infix  6 "\\/") p q
    | Imp(p, q) ->  bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff(p, q) ->  bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall(_, _) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists(_, _) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
    | Undet -> print_string "undet"
  and print_qnt qname (bvs,bod) =
    print_string qname;
    ignore (List.map (fun v -> print_string " "; print_string v) bvs);
    print_string "."; Format.print_space(); Format.open_box 0;
    print_formula 0 bod;
    Format.close_box()
  and print_prefix newpr sym p =
   print_string sym; print_formula (newpr+1) p
  and print_infix newpr sym p q =
    print_formula (newpr+1) p;
    print_string(" "^sym); Format.print_space();
    print_formula newpr q in
  print_formula 0

let get_simulax_guard pfn =
  let rec get_simulax_guard_rec fm =
    match fm with
    | False -> "(constant false)"
    | True -> "(constant true)"
    | Atom(pargs) -> pfn pargs
    | Not(p) -> "(operator not "^(get_simulax_guard_rec p)^")"
    | And(p, q) -> "(operator and "^(get_simulax_guard_rec p)^" "^(get_simulax_guard_rec q)^")"
    | Or(p, q) ->  "(operator or "^(get_simulax_guard_rec p)^" "^(get_simulax_guard_rec q)^")"
    | Imp(p, q) ->  "(operator implies "^(get_simulax_guard_rec p)^" "^(get_simulax_guard_rec q)^")"
    | Iff(_, _) -> failwith "iff not supported by SMT"
    | Forall(_, _) -> failwith "quantification not supported by SMT"
    | Exists(_, _) -> failwith "quantification not supported by SMT"
    | Undet -> failwith "undet not supported by SMT" in
  get_simulax_guard_rec

let print_qformula pfn fm =
  Format.open_box 0; print_string "<<";
  Format.open_box 0; print_formula pfn fm; Format.close_box();
  print_string ">>"; Format.close_box();;

let check_skolem_prenex fml = 
  let rec check_skolem fml fa_okay =
    match fml with
    | Undet | False | True | Atom(_) -> true
    | Not(x) -> (check_skolem x false)
    | And(x, y) | Or(x, y) | Iff(x, y) | Imp(x, y) 
      -> ((check_skolem x false) && (check_skolem y false))
    | Forall(_, subfml) -> (if fa_okay then (check_skolem subfml true) else false)
    | Exists(_, _) -> false
  in check_skolem fml true

let get_fa_vars fml = 
  let rec get_fa_vars_rec fml acc =
    match fml with
    | Forall(x, subfml) -> (get_fa_vars_rec subfml (List.append [x] acc))
    | _ -> acc in 
  if (check_skolem_prenex fml) then get_fa_vars_rec fml [] 
  else failwith "get_fa_vars non-skolem-prenex"

let num_fa_vars fml = List.length (get_fa_vars fml)

let simplify fml = 
  let rec simplify_rec fml = 
  match fml with
    | And(x, y) -> simplify_and (simplify_rec x) (simplify_rec y)
    | Or(x, y) -> simplify_or (simplify_rec x) (simplify_rec y)
    | Imp(x, y) -> simplify_imp (simplify_rec x) (simplify_rec y)
    | Iff(x, y) -> simplify_iff (simplify_rec x) (simplify_rec y)
    | Not(x) -> simplify_not (simplify_rec x)
    | fml -> fml
  and simplify_and x y =
    match x, y with
    | _, False -> False
    | False, _ -> False
    | y, True ->  y
    | True, y -> y
    | x, y -> And(x, y)
  and simplify_or x y =
    match x, y with
    | x, False -> x
    | False, y -> y
    | _, True -> True
    | True, _ -> True
    | x, y -> Or(x, y)
  and simplify_not x =
    match x with
    | True -> False
    | False -> True
    | x -> Not(x)
  and simplify_imp x y =
    match x, y with
    | False, _ -> True
    | _, True ->  True
    | x, False -> Not(x)
    | True, y -> y
    | x, y -> Imp(x, y)
  and simplify_iff x y =
    match x, y with
    | False, y -> Not(y)
    | x, False -> Not(x)
    | True, y -> y
    | x, True -> x
    | x, y -> Iff(x, y) in
  simplify_rec fml
  