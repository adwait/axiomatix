let warning x ss =
  BackendLinux.printfFlush x ("Warning: " ^ ss)

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)
let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

(** val rev' : 'a1 list -> 'a1 list **)
let rev' l =
  rev_append l []

(** val rangeHelper : int -> int list -> int list **)
let rec rangeHelper n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    l)
    (fun n' ->
    rangeHelper n' (n'::l))
    n0

(** val range : int -> int list **)
let range n0 =
  rangeHelper n0 []

(** val mapHelper : ('a1 -> 'a2) -> 'a1 list -> 'a2 list -> 'a2 list **)
let rec mapHelper f l l' =
  match l with
  | [] -> rev' l'
  | h::t -> mapHelper f t ((f h)::l')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)
let map f l =
  mapHelper f l []
