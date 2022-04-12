open USpecLang
open Utils

type elemvar = string
type varlist = elemvar list
type skfmap = elemvar -> varlist
type renamemap = elemvar -> elemvar
type varcontext = {
  uVars : varlist;
  eVars : varlist;
  renameMap : renamemap;
  skfMap : skfmap;
}

(* Add a new universally quantified variable newv (renamed to newname) to the context *)
let addUvar (varcxt : varcontext) (newv : elemvar) (newname : elemvar) : varcontext = 
  let newMap ev : elemvar =
    if ev = newv then newname else (varcxt.renameMap ev) in 
  { 
    uVars = newv::varcxt.uVars; 
    eVars = varcxt.eVars; 
    renameMap = newMap;
    skfMap = varcxt.skfMap
  }
(* Add a new existentially quantified variable newv (renamed to newname) to the context *)
let addEvar (varcxt : varcontext) (newv : elemvar) (newname : elemvar) (deplist : varlist) : varcontext = 
  let newMap ev : varlist = 
    if ev = newv then deplist else (varcxt.skfMap ev) in
    let newRenameMap ev : elemvar =
      if ev = newv then newname else (varcxt.renameMap ev) in
  { 
    uVars = varcxt.uVars; 
    eVars = newv::varcxt.eVars; 
    renameMap = newRenameMap;
    skfMap = newMap
  }

(* Empty type variables: for initialization *)
let emptystate : fOLState = { 
    stateNodes = [];
    stateNotNodes = [];
    stateEdgeNodes = [];
    stateEdges = []; 
    stateUops = [];
    stateInitial = [];
    stateFinal = [];
    stateArchEdges = [] 
  }
let emptyskfmap _ : varlist = []
let emptyrenamemap _ : elemvar = ""
let emptyvarcontext = {
    uVars = [];
    eVars = [];
    renameMap = emptyrenamemap;
    skfMap = emptyskfmap
  }

let rec recBinOp op lst =
  match lst with
  | [] -> failwith "list_max called on empty list"
  | [x] -> x
  | h::t -> "(" ^ op ^ " " ^ h ^ " " ^ (recBinOp op t) ^ ")"

type predGraphNode = (string, (stringOrInt, stringOrInt) prod) prod
type predGraphEdge =
  (((predGraphNode, predGraphNode) prod, string) prod, string) prod

let convertNodeToLisp (cxt : varcontext) (n : predGraphNode) = 
  match n with
  | Pair (_, b) -> match b with
    | Pair (i, s) -> (cxt.renameMap (soiToString i)) ^ "." ^ (soiToString s)
let convertEdgeToLisp (cxt : varcontext) (e : predGraphEdge) =
  match e with
  | Pair (a, _) -> match a with
    | Pair(b, _) -> match b with
    | Pair(e1, e2) -> 
  "(hb" ^ " " ^ (convertNodeToLisp cxt e1) ^ " " ^ (convertNodeToLisp cxt e2) ^ ")"


(* Add support for more predicates here *)
let convertPredToLisp (pred : fOLPredicateType) (cxt : varcontext) : string =
  match pred with
  | PredDebug a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredHasDependency (a, b, c) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ " " ^ (cxt.renameMap c) ^ ")"
  | PredIsRead a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredIsWrite a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredIsAPICAccess (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredIsFence a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredAccessType (a, b) -> "(" ^ (predToName pred) ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredProgramOrder (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredConsec (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameUop (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameNode (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameCore (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap (soiToString a)) ^ " " ^ (cxt.renameMap (soiToString b)) ^ ")"
  | PredSmallerGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameIntraInstID (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (soiToString b) ^ ")"
  | PredOnCore (_, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredOnThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSamePhysicalAddress (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredSameVirtualAddress (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredKnownData a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredSameData (a, b) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ " " ^ (cxt.renameMap b) ^ ")"
  | PredDataFromPAInitial a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredTrue -> "True"
  | PredFalse -> "False"
  | PredAddEdges lst -> (recBinOp "and" (map (convertEdgeToLisp cxt) lst))
  | PredEdgesExist lst -> (recBinOp "and" (map (convertEdgeToLisp cxt) lst))
  | PredDataFromPAFinal a -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | PredCustom (_, a) -> "(" ^ (predToName pred) ^ " " ^ (cxt.renameMap a) ^ ")"
  | _ -> warning " error in convertPredToLisp" (" Predicate " ^ (predToName pred) ^ " not supported ")

(* Not really being used *)
type jsonT =
  | JAssoc of (string * jsonT) list
  | JList of jsonT list
  | JString of string
  | JFloat of float
  | JInt of int
  | JBool of bool
  | JNull

let rec pretty_string (json : jsonT) : string =
  let rec get_assoc_string (assoc_list : (string * jsonT) list) : string =
    match assoc_list with
    | [] -> "\n"
    | h::t -> "\t" ^ (fst h) ^ ":" ^ (pretty_string (snd h)) ^ "\n" ^ 
      (get_assoc_string t)
  and get_list_string (a : jsonT list) : string =
    match a with
    | [] -> ""
    | [x] -> (pretty_string x)
    | h::t -> (pretty_string h) ^ ",\n" ^ (get_list_string t)
  in  match json with 
  | JAssoc a -> "{\n" ^ (get_assoc_string a) ^ "}"
  | JList a -> "[" ^ (get_list_string a) ^ "]"
  | JString a -> "\"" ^ a ^ "\""
  | JFloat a -> string_of_float a
  | JInt a -> string_of_int a
  | JBool a -> string_of_bool a
  | JNull -> ""

(* Manually generate json expression for string *)
let get_json_for_string (s : string) : string =
  "\"" ^ s ^ "\""

(* Manually generate json expression for list of strings *)
let rec get_json_for_seq (a : string list) : string =
  match a with
  | [] -> ""
  | [x] -> "\"" ^ x ^ "\""
  | h::t -> "\"" ^ h ^ "\"" ^ ", " ^ (get_json_for_seq t)

(* Manually generate json expression for dictionary from string to list of strings *)
let get_json_for_map (cxt : varcontext) : string =
  let rec get_skfmap_helper (evarl : varlist) =  
    match evarl with
    | [] -> ""
    | [x] -> "\"" ^ (cxt.renameMap x) ^ "\" : [" ^ (get_json_for_seq (List.map cxt.renameMap (cxt.skfMap x))) ^ "]"
    | h::t -> "\"" ^ (cxt.renameMap h) ^ "\"" ^ " : [" ^ (get_json_for_seq (List.map cxt.renameMap (cxt.skfMap h))) ^ "]," ^ " " ^ (get_skfmap_helper t)
  in get_skfmap_helper (cxt.eVars)

let get_single_axiom_string (name : elemvar) (cxt : varcontext) (fmlstring : string) : string =
  let uvars = "[" ^ (get_json_for_seq (List.map (cxt.renameMap) cxt.uVars)) ^ "]"
  and evars = "[" ^ (get_json_for_seq (List.map (cxt.renameMap) cxt.eVars)) ^ "]"
  in "\t" ^ (get_json_for_string name) ^ " : " ^ "{\n\t\t" ^ "\"uVars\" : " ^ uvars ^ ",\n\t\t" ^
    "\"eVars\" : " ^ evars ^ ",\n\t\t" ^ "\"skfMap\" : " ^ "{" ^ (get_json_for_map cxt)
    ^  "},\n\t\t" ^ "\"formula\" : " ^ (get_json_for_string fmlstring) ^ "\n\t}"

let rec convertFmlToLisp (fml : fOLFormula) (cxt : varcontext) : string * varcontext =
  match fml with
  | FOLName (name, subf) -> 
    let subfml = (convertFmlToLisp subf cxt) in
    (get_single_axiom_string name (snd subfml) (fst subfml)), (snd subfml)
  (* "(" ^ name ^ " " ^ (convertFmlToLisp subf cxt) ^ ")" *)
  | FOLAnd (sub1, sub2) -> 
    let subfml1 = (convertFmlToLisp sub1 cxt) in 
    let subfml2 = (convertFmlToLisp sub2 (snd subfml1)) in 
    "(and " ^ (fst subfml1) ^ "  " ^ (fst subfml2) ^ ")" , (snd subfml2)
  | FOLOr (sub1, sub2) -> 
    let subfml1 = (convertFmlToLisp sub1 cxt) in 
    let subfml2 = (convertFmlToLisp sub2 (snd subfml1)) in 
    "(or " ^ (fst subfml1) ^ "  " ^ (fst subfml2) ^ ")" , (snd subfml2)
  | FOLNot sub1 -> 
    let subfml1 = (convertFmlToLisp sub1 cxt) in 
    "(not " ^ (fst subfml1) ^ ")", (snd subfml1)
  | FOLPredicate pred -> 
    (convertPredToLisp pred cxt), cxt
  | FOLForAll (quant, subf) -> 
    let newname = "i" ^ (string_of_int ((List.length cxt.uVars) + 1)) in
    (convertFmlToLisp subf (addUvar cxt (first (quant emptystate [])) newname))
  | FOLExists (quant, subf) ->
    let newname = "sk" ^ (string_of_int ((List.length cxt.eVars) + 1)) in
    (convertFmlToLisp subf (addEvar cxt (first (quant emptystate [])) newname cxt.uVars))
  | _ -> warning (" error in convertFmlToLisp " , emptyvarcontext) " Fml not supported "

let convertStageToLisp (st) : string = 
  match st with
  | StageNameTerm (evar, _) -> evar
  | _ -> warning " error in convertStageToLisp " " should not reach here "
  

(* Top-level function: converts a single axiomatic model to json+lisp format *)
let convertToLisp (name : string) (comp : microarchitecturalComponent) : string =
  let rec recConvertToLisp (c : microarchitecturalComponent) : (string list * string) =
    match c with
    | [] -> ([], "")
    | [x] -> (match x with
      | FOLAxiom ax -> ([], (fst (convertFmlToLisp ax emptyvarcontext)))
      | FOLContextTerm cterm -> (match cterm with
        | StageNameTerm (_, _) -> ([(convertStageToLisp cterm)], "")
        | _ -> warning ([], " error in convertToLisp ") " is not a StageNameTerm ")
      | _ -> warning ([], " error in convertToLisp ") " Is not axiom or stageName ")
    | h::t -> (match h with
      | FOLAxiom ax -> let remaining = (recConvertToLisp t) in
        ((fst remaining), (fst (convertFmlToLisp ax emptyvarcontext)) ^ ",\t\n" ^ (snd remaining))
      | FOLContextTerm cterm -> (match cterm with
        | StageNameTerm (_, _) -> let remaining = (recConvertToLisp t) in 
          ((convertStageToLisp cterm)::(fst remaining), (snd remaining))
        | _ -> warning ([], " error in convertToLisp ") " is not a StageNameTerm "
        )
      | _ -> warning ([], " error in convertToLisp ") " Is not axiom or stageName ") and
  header = "\"name\" : \"" ^ name ^ "\",\n"
  in
  let parsedModel = (recConvertToLisp comp) in
   "{\n" ^ header ^ 
   "\"axioms\" : {\n" ^ (snd parsedModel) ^ "\n}" ^ ",\n" ^ 
   "\"stages\" : [" ^ (get_json_for_seq (fst parsedModel)) ^ "]" ^ "\n}"
  