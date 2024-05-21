exception Not_Implemented

(* Lists *)
type 'a list_t =
  | Cons of 'a * 'a list_t
  | Nil

let rec fold list cons_fn nil_val =
  match list with
  | Cons (head, tail) -> cons_fn head (fold tail cons_fn nil_val)
  | Nil -> nil_val

let push elem list =
  fold list (fun head tail -> Cons (head, tail)) (Cons (elem, Nil))

(* Terms *)
type term =
  | Var of string * int
  | Set
  | All of string * term * (term -> term)
  | Lam of string * (term -> term)
  | App of term * term
  | Fix of string * term * (term -> term)
  | Slf of string * (term -> term)
  | Ins of term
  | Ann of bool * term * term
  | Let of string * term * (term -> term)
  | Def of string * term * (term -> term)
  | Ref of string
  | Hol of string * context * term list_t

and context = (string * term) list_t

type def = { typ: term; val_: term }
type book = (string, def) Hashtbl.t
type load = string -> (def option)
type fill = (string, term) Hashtbl.t

(* Checker *)
(* Reduces to weak normal form *)
(* let rec reduce load term dep = *)