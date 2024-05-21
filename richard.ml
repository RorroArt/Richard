exception Not_Implemented
exception Type_Error of string
exception Type_Mismatch of string

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

(* these functions should go into a parsing file or something *)
let show_term (term: term) (dep: int): string = raise Not_Implemented

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

  exception InferenceError of string

  (* Checker *)
  let rec infer ?(dep: int = 0) (fill: fill) (load: load) (term: term) : term =
    match term with
    | Var _ -> raise (InferenceError "Can't infer var.")
    | Ref nam ->
        (match load nam with
         | Some loaded -> loaded.typ
         | None -> Ref nam)
    | Hol (nam, ctx, cap) -> Hol (nam ^ "_T", ctx, cap)
    | Set -> Set
    | All (nam, inp, bod) ->
        ignore (check fill load inp Set true dep);
        ignore (check fill load (bod (Ann (false, Var (nam, dep), inp))) Set true (dep + 1));
        Set
    | Lam (nam, bod) ->
        All (nam,
          Hol (nam ^ "_I", Nil, Nil),
          (fun x -> Hol (nam ^ "_O", Cons ((nam, x), Nil), Nil)))
    | App (fun_term, arg_term) ->
        let fun_ty = reduce load (infer fill load fun_term ~dep) dep in
        let fun_ty = match fun_ty with
          | Hol (nam, ctx, cap) ->
              All (nam,
                Hol (nam ^ "_I", ctx, cap),
                (fun x -> Hol (nam ^ "_O", Cons ((nam, x), ctx), cap)))
          | _ -> fun_ty
        in
        (match fun_ty with
         | All (_, inp, bod) ->
             ignore (check fill load arg_term inp true dep);
             bod arg_term
         | _ ->
             print_endline ("- fun: " ^ show_term fun_term dep);
             print_endline ("- typ: " ^ show_term fun_ty dep);
             raise (InferenceError "NonFunApp"))
    | Fix (_, typ, bod) ->
        infer fill load (bod (Ann (false, Var ("", dep), typ))) ~dep:(dep + 1)
    | Ins val_ ->
        let val_ty = reduce load (infer fill load val_ ~dep) dep in
        (match val_ty with
         | Slf (_, bod) -> bod term
         | _ -> raise (InferenceError "NonSlfIns"))
    | Slf (nam, bod) ->
        ignore (check fill load (bod (Ann (false, Var (nam, dep), term))) Set true dep);
        Set
    | Ann (_, val_, typ) ->
        check fill load val_ typ true dep
    | Let _ -> raise (InferenceError "NonAnnLet")
    | Def _ -> raise (InferenceError "NonAnnDef")
  
  (* Assume check exists and has the expected signature *)
and check (fill: fill) (load: load) (val_: term) (tty: term) (chk: bool) (dep: int) : term =
  let typ = reduce load tty dep in
  match chk with 
  | false -> typ
  | true -> 
    (match val_ with
    | Lam (nam, bod) ->
        (match typ with
          | All (typ_nam, inp, typ_bod) ->
              ignore (check fill load (bod (Ann (false, Var(nam, dep), inp))) (typ_bod (Ann(false, Var(typ_nam, dep), inp))) chk (dep + 1));
              typ
          | _ ->
              raise (Type_Error "NonFunLam"))
    | Ins val_inner ->
        (match typ with
          | Slf (nam, bod_typ) ->
              ignore (check fill load val_inner (bod_typ val_) chk dep);
              typ
          | _ ->
              raise (Type_Error "NonSlfIns"))
    | Hol (nam, ctx, cap) ->
        (* Implement fill_typed_hole here *)
        typ
    | Let (nam, val_inner, bod) ->
        let val_typ = infer ~dep fill load val_inner in
        ignore (check fill load (bod (Ann (false, val_inner, val_typ))) typ chk (dep + 1));
        typ
    | Def (nam, val_inner, bod) ->
        ignore (check fill load (bod val_inner) typ chk (dep + 1));
        typ
    | _ ->
        let inf = infer ~dep fill load val_ in
        let inf = reduce load inf dep in
        (match (equal (Some fill) load typ inf dep) with
        | true -> typ
        | false ->
            let exp = show_term val_ dep in
            let det = show_term tty dep in
            let msg = "TypeMismatch\n- expected: " ^ exp ^ "\n- detected: " ^ det in
            raise (Type_Mismatch msg)
        ))

