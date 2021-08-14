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
  skfMap : skfmap
}

let addUvar (varcxt : varcontext) (newv : elemvar) (newname : elemvar) : varcontext = 
  let newMap ev : elemvar =
    if ev = newv then newname else (varcxt.renameMap ev) in 
  { 
    uVars = newv::varcxt.uVars; 
    eVars = varcxt.eVars; 
    renameMap = newMap;
    skfMap = varcxt.skfMap
  }
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

let convertNodeToLisp (n : predGraphNode) = 
  match n with
  | Pair (_, b) -> match b with
    | Pair (i, s) -> (soiToString i) ^ "." ^ (soiToString s)
let convertEdgeToLisp (e : predGraphEdge) =
  match e with
  | Pair (a, _) -> match a with
    | Pair(b, _) -> match b with
    | Pair(e1, e2) -> 
  "(hb" ^ " " ^ (convertNodeToLisp e1) ^ " " ^ (convertNodeToLisp e2) ^ ")"


let convertPredToLisp (pred : fOLPredicateType) (_ : varcontext) : string =
  match pred with
  | PredDebug a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredHasDependency (a, b, c) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
  | PredIsRead a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredIsWrite a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredIsAPICAccess (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredIsFence a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredAccessType (a, b) -> "(" ^ (predToName pred) ^ a ^ " " ^ b ^ ")"
  | PredProgramOrder (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredConsec (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameUop (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameNode (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b^ ")"
  | PredSameCore (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (soiToString b) ^ ")"
  | PredSmallerGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameIntraInstID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (soiToString b) ^ ")"
  | PredOnCore (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ b ^ ")"
  | PredOnThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ b ^ ")"
  | PredSamePhysicalAddress (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameVirtualAddress (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredKnownData a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredSameData (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredDataFromPAInitial a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredTrue -> "True"
  | PredFalse -> "False"
  | PredAddEdges lst -> (recBinOp "and" (map (convertEdgeToLisp) lst))
  | PredEdgesExist lst -> (recBinOp "and" (map (convertEdgeToLisp) lst))
  | PredDataFromPAFinal a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | _ -> warning " error in convertPredToLisp" (" Predicate " ^ (predToName pred) ^ " not supported ")

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

let get_json_for_string (s : string) : string =
  "\"" ^ s ^ "\""

let rec get_json_for_seq (a : string list) : string =
  match a with
  | [] -> ""
  | [x] -> "\"" ^ x ^ "\""
  | h::t -> "\"" ^ h ^ "\"" ^ ", " ^ (get_json_for_seq t)
    
let get_single_axiom_string (name : elemvar) (cxt : varcontext) (fmlstring : string) : string =
  let uvars = "[" ^ (get_json_for_seq cxt.uVars) ^ "]"
  and evars = "[" ^ (get_json_for_seq cxt.eVars) ^ "]"
  in "\t" ^ (get_json_for_string name) ^ " : " ^ "{\n\t\t" ^ "\"uVars\" : " ^ uvars ^ ",\n\t\t" ^
    "\"eVars\" : " ^ evars ^ ",\n\t\t" ^ "\"skfMap\" : " ^ "{},\n\t\t" ^
    "\"formula\" : " ^ (get_json_for_string fmlstring) ^ "\n\t}"

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
    let newname = "i" ^ (string_of_int (List.length cxt.uVars)) in
    (convertFmlToLisp subf (addUvar cxt (first (quant emptystate [])) newname))
  | FOLExists (quant, subf) ->
    let newname = "i" ^ (string_of_int (List.length cxt.eVars)) in
    (convertFmlToLisp subf (addEvar cxt (first (quant emptystate [])) newname cxt.uVars))
  | _ -> warning (" error in convertFmlToLisp " , emptyvarcontext) " Fml not supported "

let convertToLisp (comp : microarchitecturalComponent) : string =
  let rec recConvertToLisp (c : microarchitecturalComponent) : string =
    match c with
    | [] -> ""
    | [x] -> (match x with
      | FOLAxiom ax -> (fst (convertFmlToLisp ax emptyvarcontext))
      | _ -> warning " error in convertToLisp " " Is not axiom ")
    | h::t -> match h with
      | FOLAxiom ax -> 
        (fst (convertFmlToLisp ax emptyvarcontext)) ^ ",\t\n" ^ (recConvertToLisp t)
      | _ -> warning " error in convertToLisp " " Is not axiom " 
    in
  "{\n" ^ (recConvertToLisp comp) ^ "\n}"
  