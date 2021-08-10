open USpecLang
open Utils

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


let convertPredToLisp (pred : fOLPredicateType) : string =
  match pred with
  | PredDebug a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredHasDependency (a, b, c) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ " " ^ c ^ ")"
  | PredIsRead a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredIsWrite a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredIsAPICAccess (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredIsFence a -> "(" ^ (predToName pred) ^ " " ^ a ^ ")"
  | PredAccessType (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameUop (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameNode (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b^ ")"
  | PredSameCore (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (soiToString b) ^ ")"
  | PredSmallerGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameGlobalID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameIntraInstID (a, b) -> "(" ^ (predToName pred) ^ " " ^ a ^ " " ^ b ^ ")"
  | PredSameThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ (soiToString b) ^ ")"
  | PredOnCore (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ b ^ ")"
  | PredOnThread (a, b) -> "(" ^ (predToName pred) ^ " " ^ (soiToString a) ^ " " ^ b ^ ")"
  | PredTrue -> "True"
  | PredFalse -> "False"
  | PredEdgesExist lst -> (recBinOp "and" (map (convertEdgeToLisp) lst))
  | PredAddEdges lst -> (recBinOp "and" (map (convertEdgeToLisp) lst))
  | _ -> warning " error in convertPredToLisp" (" Predicate " ^ (predToName pred) ^ " not supported ")

let rec convertFmlToLisp (fml : fOLFormula) : string =
  match fml with
  | FOLName (name, subf) -> "(" ^ name ^ " " ^ (convertFmlToLisp subf) ^ ")"
  | FOLAnd (sub1, sub2) -> "(and " ^ (convertFmlToLisp sub1) ^ "  " ^ (convertFmlToLisp sub2) ^ ")"
  | FOLOr (sub1, sub2) -> "(or " ^ (convertFmlToLisp sub1) ^ "  " ^ (convertFmlToLisp sub2) ^ ")"
  | FOLNot sub1 -> "(not " ^ (convertFmlToLisp sub1) ^ ")"
  | FOLPredicate pred -> (convertPredToLisp pred)
  | _ -> warning " error in convertFmlToLisp " " Fml not supported "

let convertToLisp folStmt : string =
  match folStmt with
  | FOLAxiom fol -> convertFmlToLisp fol
  | _ -> warning " error in convertToLisp " " Is not axiom "
  