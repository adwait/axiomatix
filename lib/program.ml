type core = Core of int

type variable = Address of int
type value = Value of int

type itype =
  | Read
  | Write

type metadata = 
  | Read of variable * value
  | Write of variable * value

type instruction = Instruction of core * int * metadata
let type_of_instruction inst : itype =
  match inst with
  | Instruction(_, _, Read(_, _)) -> Read
  | Instruction(_, _, Write(_, _)) -> Write

let coreOf inst =
  match inst with
  | Instruction(x, _, _) -> x

type stage = 
  | Fetch
  | Decode
  | Execute

type event = 
  | InitEvent
  | Event of instruction * stage
let type_of_event ev : itype =
  match ev with
  | InitEvent -> Write
  | Event(inst, _) -> (type_of_instruction inst)