type 'a list_t =
  | Cons of 'a * 'a list_t
  | Nil

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
  | Hol of string * context * (term list_t)
and context = (string * term) list_t