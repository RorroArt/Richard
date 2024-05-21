exception Not_Implemented
exception Type_Error of string

(* Types *)
(* Lists *)
type 'a list_t =
  | Cons of 'a * 'a list_t
  | Nil

let rec fold (list: 'a list_t) (f: 'a -> 'acc -> 'acc) (acc: 'acc) =
  match list with
  | Cons (head, tail) -> f head (fold tail f acc)
  | Nil -> acc

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
  | Hol of string * context * (term list_t)

and context = (string * term) list_t

type def = { typ: term; val_: term }
type book = (string, def) Hashtbl.t
type load = string -> (def option)
type fill = (string, term) Hashtbl.t

(* Checker *)
(* Reduces to weak normal form *)
let rec reduce (load: load) (term: term) (dep: int): term =
  match term with
  | App (fun_term, arg_term) ->
      let fun_reduced = reduce load fun_term dep in
      (match fun_reduced with
       | Lam (_, bod) -> reduce load (bod arg_term) dep
       | Hol (nam, ctx, cap) -> reduce load (Hol (nam, ctx, push arg_term cap)) dep
       | _ -> term)
  | Fix (_, _, bod) -> reduce load (bod term) dep
  | Ann (_, val_, _) -> reduce load val_ dep
  | Ins val_ -> reduce load val_ dep
  | Let (_, val_, bod) -> reduce load (bod val_) dep
  | Def (_, val_, bod) -> reduce load (bod val_) dep
  | Ref nam ->
      (match load nam with
       | Some loaded -> reduce load loaded.val_ dep
       | None -> term)
  | _ -> term

let rec equal (fill: fill option) (load: load) (a: term) (b: term) (dep: int) : bool =
  let rec compare xs ys =
    match xs, ys with
    | Cons (head_x, tail_x), Cons (head_y, tail_y) ->
        let head_eq = equal fill load head_x head_y dep in
        let tail_eq = compare tail_x tail_y in
        head_eq && tail_eq
    | Nil, Nil -> true
    | _ -> false
  in
  let rec get_args = function
    | App (fun_, arg) -> Cons (arg, get_args fun_)
    | _ -> Nil
  in
  let eq = match a, b with
    | Var (_, val_a), Var (_, val_b) -> val_a = val_b
    | Set, Set -> true
    | All (nam_a, inp_a, bod_a), All (nam_b, inp_b, bod_b) ->
        equal fill load inp_a inp_b dep &&
        equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
    | Lam (nam_a, bod_a), Lam (nam_b, bod_b) ->
        equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
    | App (fun_a, arg_a), App (fun_b, arg_b) ->
        equal fill load fun_a fun_b dep && equal fill load arg_a arg_b dep
    | Fix (nam_a, typ_a, bod_a), Fix (nam_b, typ_b, bod_b) ->
        equal fill load typ_a typ_b dep &&
        equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
    | Slf (nam_a, bod_a), Slf (nam_b, bod_b) ->
        equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
    | Ins val_a, Ins val_b ->
        equal fill load val_a val_b dep
    | Ref nam_a, Ref nam_b ->
        nam_a = nam_b
    | Hol (nam_a, _, _), Hol (nam_b, _, _) ->
        nam_a = nam_b
    | Hol (_, _, a_cap), _ ->
        (match fill with
        | Some fill_tbl ->
            (* Implement fill_valued_hole here *)
            true
        | None ->
            let b_cap = get_args b in
            compare a_cap b_cap)
    | _, Hol _ ->
        equal fill load b a dep
    | _ -> false
  in
  (* Could make this better with matches*)
  if not eq then
    let a2 = reduce load a dep in
    if a2 <> a then
      equal fill load a2 b dep
    else
      let b2 = reduce load b dep in
      if b2 <> b then
        equal fill load a b2 dep
      else
        eq
  else
    eq

(* not super sure what the depth is used for *)
let rec normal ?(dep=0) (load: load) (term: term): term =
  let term = reduce load term dep in
  match term with
  | All (nam, inp, bod) ->
      All (nam, normal ~dep load inp, fun x -> normal ~dep:(dep + 1) load (bod x))
  | Lam (nam, bod) ->
      Lam (nam, fun x -> normal ~dep:(dep + 1) load (bod x))
  | App (fun_term, arg_term) ->
      App (normal ~dep load fun_term, normal ~dep load arg_term)
  | Fix (nam, typ, bod) ->
      Fix (nam, normal ~dep load typ, fun x -> normal ~dep:(dep + 1) load (bod x))
  | Ann (_, val_, _) ->
      normal ~dep load val_
  | Let (_, val_, bod) ->
      normal ~dep load (bod val_)
  | Def (_, val_, bod) ->
      normal ~dep load (bod val_)
  | _ -> term

let rec infer ?(dep=0) (fill: fill) (load: load) (term: term): term =
  match term with
  | Var _ -> raise (Type_Error "Can't infer type of variable.")
  | Ref name -> let loaded = load name in
      (match loaded with
       | Some def -> def.typ
       | None -> raise (Type_Error "Can't infer type of reference."))
  | _ -> raise Not_Implemented

