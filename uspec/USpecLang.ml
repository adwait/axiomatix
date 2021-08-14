open Utils

type ('a, 'b) prod =
| Pair of 'a * 'b

let first (pr : ('a, 'b) prod) : 'a =
  match pr with
  | Pair (x, _) -> x

type stringOrInt =
| SoISum of stringOrInt * stringOrInt
| SoIString of string
| SoIInt of int
| SoICoreID of string

type accessedStatus =
| Accessed
| NotAccessed
| AccessedDontCare

type dirtyStatus =
| Dirty
| NotDirty
| DirtyDontCare

type instID = int
type threadID = int
type intraInstructionID = int
type index = int

type virtualTag = int
type virtualAddress = { vtag : virtualTag; vindex : index }

type physicalTag =
| PTag of int
| PTETag of virtualTag
| APICTag of string * int
type physicalAddress = { ptag : physicalTag; pindex : index }

type pTEStatus = { accessed : bool; dirty : bool }

type location = (int, int) prod
type data =
| UnknownData
| NormalData of int
| PageTableEntry of virtualTag * physicalTag * pTEStatus
| OtherData of string * int

type boundaryCondition = (physicalAddress, data) prod

type memoryAccess =
| Read of string list * virtualAddress * physicalAddress * data
| Write of string list * virtualAddress * physicalAddress * data
| Fence of string list
| FenceVA of string list * virtualAddress

type microop = { 
  globalID : instID; 
  coreID : int; 
  threadID0 : threadID;
  intraInstructionID0 : intraInstructionID;
  access : memoryAccess }

type graphNode = (microop, location) prod
type graphEdge = (((graphNode, graphNode) prod, string) prod, string) prod

type predGraphNode = (string, (stringOrInt, stringOrInt) prod) prod
type predGraphEdge =
  (((predGraphNode, predGraphNode) prod, string) prod, string) prod

type architectureLevelEdge = ((int, int) prod, string) prod

type fOLState = { stateNodes : graphNode list;
  stateNotNodes : graphNode list;
  stateEdgeNodes : graphNode list;
  stateEdges : graphEdge list; 
  stateUops : microop list;
  stateInitial : boundaryCondition list;
  stateFinal : boundaryCondition list;
  stateArchEdges : architectureLevelEdge list }

type fOLPredicateType =
| PredDebug of string
| PredHasDependency of string * string * string
| PredIsRead of string
| PredIsWrite of string
| PredIsAPICAccess of string * string
| PredIsFence of string
| PredAccessType of string * string
| PredSameUop of string * string
| PredSameNode of string * string
| PredSameCore of stringOrInt * stringOrInt
| PredSmallerGlobalID of string * string
| PredSameGlobalID of string * string
| PredSameIntraInstID of string * string
| PredSameThread of stringOrInt * stringOrInt
| PredOnCore of stringOrInt * string
| PredOnThread of stringOrInt * string
| PredSameVirtualAddress of string * string
| PredSamePhysicalAddress of string * string
| PredSameVirtualTag of string * string
| PredSamePhysicalTag of string * string
| PredSameIndex of string * string
| PredKnownData of string
| PredSameData of string * string
| PredDataFromPAInitial of string
| PredDataFromPAFinal of string
| PredSamePAasPTEforVA of string * string
| PredDataIsCorrectTranslation of accessedStatus * dirtyStatus * string
   * string
| PredTranslationMatchesInitialState of accessedStatus * dirtyStatus * string
| PredProgramOrder of string * string
| PredConsec of string * string
| PredAddEdges of predGraphEdge list
| PredEdgesExist of predGraphEdge list
| PredNodesExist of predGraphNode list
| PredTrue
| PredFalse
| PredHasID of int * int * int * int * string
| PredHasGlobalID of int * string

type fOLTerm =
| IntTerm of string * int
| StageNameTerm of string * int
| MicroopTerm of string * microop
| NodeTerm of string * graphNode
| EdgeTerm of string * graphEdge
| MacroArgTerm of string * stringOrInt

type fOLQuantifier = fOLState -> fOLTerm list -> (string, fOLTerm list) prod

type fOLFormula =
| FOLName of string * fOLFormula
| FOLExpandMacro of string * stringOrInt list
| FOLPredicate of fOLPredicateType
| FOLNot of fOLFormula
| FOLOr of fOLFormula * fOLFormula
| FOLAnd of fOLFormula * fOLFormula
| FOLForAll of fOLQuantifier * fOLFormula
| FOLExists of fOLQuantifier * fOLFormula
| FOLLet of fOLTerm * fOLFormula

let fOLImplies a b =
  FOLOr ((FOLNot a), b)

(** val fOLIff : fOLFormula -> fOLFormula -> fOLFormula **)
let fOLIff a b =
  FOLAnd ((fOLImplies a b), (fOLImplies b a))

type fOLMacro = ((string, string list) prod, fOLFormula) prod


type fOLStatement =
| FOLAxiom of fOLFormula
| FOLMacroDefinition of fOLMacro
| FOLContextTerm of fOLTerm

type microarchitecturalComponent = fOLStatement list
type microarchitecture = microarchitecturalComponent list


(* ----------------- *)
(* Lookup Predicates *)
(* ----------------- *)
let fOLLookupPredicate_IIIIS name a b c d e =
  if name = "HasID" 
    then PredHasID (a, b, c, d, e)
  else warning PredFalse ("Predicate " ^ name ^ " not found!")
    
let fOLLookupPredicate_SSS name a b c =
  if name = "HasDependency"
    then PredHasDependency(a, b, c)
else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_IS name a b = 
  match name with
  | "SameCore" -> PredSameCore ((SoIInt a), (SoIString b))
  | "SameThread" -> PredSameThread ((SoIInt a), (SoIString b))
  | "OnCore" -> PredOnCore ((SoIInt a), b)
  | "OnThread" -> PredOnThread ((SoIInt a), b)
  | "HasGlobalID" -> PredHasGlobalID (a, b)
  | _ -> warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_ADSS name a b c d =
  if name = "DataIsCorrectTranslation"
    then PredDataIsCorrectTranslation (a, b, c, d)
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_ADS name a b c = 
  if name = "TranslationMatchesInitialState"       
    then PredTranslationMatchesInitialState (a, b, c)
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_SS name a b =
  match name with
  | "IsAPICAccess"  ->  PredIsAPICAccess (a, b)
  | "FenceType" ->  PredAccessType (a, b)
  | "AccessType"  ->  PredAccessType (a, b)
  | "SameMicroop" ->  PredSameUop (a, b)
  | "SameCore"  ->  PredSameCore ((SoIString a), (SoIString b))
  | "SmallerGlobalID" ->  PredSmallerGlobalID (a, b)
  | "SameGlobalID"  ->  PredSameGlobalID (a, b)
  | "SameIntraInstructionID"  ->  PredSameIntraInstID (a, b)
  | "OnCore"  ->  PredOnCore ((SoIString a), b)
  | "SameThread"  ->  PredSameThread ((SoIString a), (SoIString b))
  | "OnThread"  ->  PredOnThread ((SoIString a), b)
  | "SameVirtualAddress"  ->  PredSameVirtualAddress (a, b)
  | "SamePhysicalAddress" ->  PredSamePhysicalAddress (a, b)
  | "SameVirtualTag"  ->  PredSameVirtualTag (a, b)
  | "SamePhysicalTag" ->  PredSamePhysicalTag (a, b)
  | "SameIndex" ->  PredSameIndex (a, b)
  | "SameData"  ->  PredSameData (a, b)
  | "SamePAasPTEforVA"  ->  PredSamePAasPTEforVA (a, b)
  | "DataIsCorrectTranslation"  ->
    let result = PredDataIsCorrectTranslation (AccessedDontCare, DirtyDontCare, a, b) 
    in warning result "DataIsCorrectTranslation: assuming accessed and dirty are don't cares"
  | "ConsecutiveMicroops" -> PredConsec (a, b)
  | "ProgramOrder"  -> PredProgramOrder (a, b)
  | _ -> warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_S name a = 
  match name with
  | "Debug" ->  PredDebug a
  | "IsRead"  ->  PredIsRead a
  | "IsAnyRead" ->  PredIsRead a
  | "IsWrite" ->  PredIsWrite a
  | "IsAnyWrite"  ->  PredIsWrite a
  | "IsFence" ->  PredIsFence a
  | "IsAnyFence"  ->  PredIsFence a
  | "KnownData" ->  PredKnownData a
  | "DataFromInitialStateAtPA"  ->      PredDataFromPAInitial a
  | "DataFromFinalStateAtPA"  ->        PredDataFromPAFinal a
  | "TranslationMatchesInitialState"  ->
    let result = PredTranslationMatchesInitialState (AccessedDontCare, DirtyDontCare, a) 
    in warning result "TranslationMatchesInitialState: assuming accessed and dirty are don't cares"
  | _ -> warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_E name a =
  if name = "AddEdge" then PredAddEdges [a]
  else if name = "EdgeExists" then PredEdgesExist [a]
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_N name a =
  if name = "NodeExists" then PredNodesExist [a]
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_lE name a =
  if name = "AddEdges" then PredAddEdges a
  else if name = "EdgesExist" then PredEdgesExist a
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

let fOLLookupPredicate_lN name a =
  if name = "NodesExist" then PredNodesExist a
  else warning PredFalse ("Predicate " ^ name ^ " not found!")

(* ------------------------------- *)
(* Helper functions for the axioms *)
(* ------------------------------- *)

(** val numCores : microop list -> int -> int **)
let rec numCores (l : microop list) n0 =
  match l with
  | [] -> n0
  | h::t -> numCores t (max n0 ((fun x -> x + 1) h.coreID))

(** val coreQuantifier : string -> fOLQuantifier **)
let coreQuantifier name s _ =
  let cores = numCores s.stateUops 0 in
  Pair (name, (map (fun x -> IntTerm (name, x)) (range cores)))

(** val numThreads : microop list -> int -> int **)
let rec numThreads l n0 =
  match l with
  | [] -> n0
  | h::t -> numThreads t (max n0 ((fun x -> x + 1) h.threadID0))

(** val threadQuantifier : string -> fOLQuantifier **)
let threadQuantifier name s _ =
  let cores = numThreads s.stateUops 0 in
  Pair (name, (map (fun x -> IntTerm (name, x)) (range cores)))

(** val microopQuantifier : string -> fOLQuantifier **)
let microopQuantifier name s _ =
  let uops = s.stateUops in
  Pair (name, (map (fun x -> MicroopTerm (name, x)) uops))

let rec soiToString (soi : stringOrInt) : string =
  match soi with
  | SoISum (a, b) -> (soiToString a) ^ ":" ^ (soiToString b)
  | SoIString a -> a
  | SoIInt a -> (string_of_int a)
  | SoICoreID a -> a

let predToName (fOLPredicate : fOLPredicateType) : string =
  match fOLPredicate with
  | PredDebug  _ -> "Debug"
  | PredHasDependency  _ -> "HasDependency"
  | PredIsRead  _ -> "IsRead"
  | PredIsWrite  _ -> "IsWrite"
  | PredIsAPICAccess  _ -> "IsAPICAccess"
  | PredIsFence  _ -> "IsFence"
  | PredAccessType  _ -> "AccessType"
  | PredSameUop  _ -> "SameUop"
  | PredSameNode  _ -> "SameNode"
  | PredSameCore  _ -> "SameCore"
  | PredSmallerGlobalID  _ -> "SmallerGlobalID"
  | PredSameGlobalID  _ -> "SameGlobalID"
  | PredSameIntraInstID  _ -> "SameIntraInstID"
  | PredSameThread  _ -> "SameThread"
  | PredOnCore  _ -> "OnCore"
  | PredOnThread  _ -> "OnThread"
  | PredSameVirtualAddress  _ -> "SameVirtualAddress"
  | PredSamePhysicalAddress  _ -> "SamePhysicalAddress"
  | PredSameVirtualTag  _ -> "SameVirtualTag"
  | PredSamePhysicalTag  _ -> "SamePhysicalTag"
  | PredSameIndex  _ -> "SameIndex"
  | PredKnownData  _ -> "KnownData"
  | PredSameData  _ -> "SameData"
  | PredDataFromPAInitial  _ -> "DataFromPAInitial"
  | PredDataFromPAFinal  _ -> "DataFromPAFinal"
  | PredSamePAasPTEforVA  _ -> "SamePAasPTEforVA"
  | PredDataIsCorrectTranslation  _ -> "DataIsCorrectTranslation"
  | PredTranslationMatchesInitialState  _ -> "TranslationMatchesInitialState"
  | PredProgramOrder  _ -> "ProgramOrder"
  | PredConsec  _ -> "Consec"
  | PredAddEdges  _ -> "AddEdges"
  | PredEdgesExist  _ -> "EdgesExist"
  | PredNodesExist  _ -> "NodesExist"
  | PredTrue  -> "True"
  | PredFalse  -> "False"
  | PredHasID  _ -> "HasID"
  | PredHasGlobalID  _ -> "HasGlobalID"
  