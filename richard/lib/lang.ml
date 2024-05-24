exception Not_Implemented
exception Type_Error of string
exception Type_Mismatch of string
exception ParseError of string
open Ast

module Lang = struct

  (* Types *)
  (* Lists *)
  (* type 'a list_t =
    | Cons of 'a * 'a list_t
    | Nil *)

  let rec fold (list: 'a list_t) (f: 'a -> 'acc -> 'acc) (acc: 'acc) =
    match list with
    | Cons (head, tail) -> f head (fold tail f acc)
    | Nil -> acc

  let push elem list =
    fold list (fun head tail -> Cons (head, tail)) (Cons (elem, Nil))

  (* Terms *)
  (* type term =
    | Var of string * int (* why does this have a depth? *)
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

  and context = (string * term) list_t *)

  type def = { typ: term; val_: term }
  type book = (string, def) Hashtbl.t
  type load = string -> (def option)
  type fill = (string, term) Hashtbl.t


  let cut str =
    if String.length str > 1 && str.[0] = '(' && str.[String.length str - 1] = ')' then
      String.sub str 1 (String.length str - 2)
    else str
  let rec show_term term dep =
    match term with
    | Var (nam, _) -> nam
    | Set -> "*"
    | All (nam, inp, bod) -> "∀(" ^ nam ^ ":" ^ show_term inp dep ^ ") " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | Lam (nam, bod) -> "λ" ^ nam ^ " " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | App (f, arg) -> "(" ^ cut (show_term f dep) ^ " " ^ show_term arg dep ^ ")"
    | Fix (nam, typ, bod) -> "μ(" ^ nam ^ ":" ^ show_term typ dep ^ ") " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | Slf (nam, bod) -> "$" ^ nam ^ " " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | Ins val_ -> "~" ^ show_term val_ dep
    | Ann (_, val_, typ) -> "{" ^ show_term val_ dep ^ ":" ^ show_term typ dep ^ "}"
    | Let (nam, val_, bod) -> "let " ^ nam ^ " = " ^ show_term val_ dep ^ " " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | Def (nam, val_, bod) -> "def " ^ nam ^ " = " ^ show_term val_ dep ^ " " ^ show_term (bod (Var (nam, dep))) (dep + 1)
    | Ref nam -> nam
    | Hol (nam, _, cap) -> "(" ^ nam ^ fold cap (fun v str -> " " ^ show_term v dep ^ str) "" ^ ")"

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
      print_endline ("equal: " ^ (show_term a 0) ^ " == " ^ (show_term b 0) ^ " at depth " ^ string_of_int dep);
      
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
        | Var (_, val_a), Var (_, val_b) -> 
            print_endline ("Comparing Vars: " ^ string_of_int val_a ^ " == " ^ string_of_int val_b);
            val_a = val_b
        | Set, Set -> 
            print_endline "Comparing Sets";
            true
        | All (nam_a, inp_a, bod_a), All (nam_b, inp_b, bod_b) ->
            print_endline "Comparing All";
            equal fill load inp_a inp_b dep &&
            equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
        | Lam (nam_a, bod_a), Lam (nam_b, bod_b) ->
            print_endline "Comparing Lam";
            equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
        | App (fun_a, arg_a), App (fun_b, arg_b) ->
            print_endline "Comparing App";
            equal fill load fun_a fun_b dep && equal fill load arg_a arg_b dep
        | Fix (nam_a, typ_a, bod_a), Fix (nam_b, typ_b, bod_b) ->
            print_endline "Comparing Fix";
            equal fill load typ_a typ_b dep &&
            equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
        | Slf (nam_a, bod_a), Slf (nam_b, bod_b) ->
            print_endline "Comparing Slf";
            equal fill load (bod_a (Var (nam_a, dep))) (bod_b (Var (nam_b, dep))) (dep + 1)
        | Ins val_a, Ins val_b ->
            print_endline "Comparing Ins";
            equal fill load val_a val_b dep
        | Ref nam_a, Ref nam_b ->
            print_endline ("Comparing Refs: " ^ nam_a ^ " == " ^ nam_b);
            nam_a = nam_b
        | Hol (nam_a, _, _), Hol (nam_b, _, _) ->
            print_endline ("Comparing Holes: " ^ nam_a ^ " == " ^ nam_b);
            nam_a = nam_b
        | Hol (_, _, a_cap), _ ->
            print_endline "Comparing Hole with non-Hole";
            (match fill with
            | Some fill_tbl ->
                (* Implement fill_valued_hole here *)
                true
            | None ->
                let b_cap = get_args b in
                compare a_cap b_cap)
        | _, Hol _ ->
            print_endline "Comparing non-Hole with Hole";
            equal fill load b a dep
        | _ -> 
            print_endline ("Comparing other: " ^ (show_term a 0) ^ " == " ^ (show_term b 0));
            print_endline "Comparison failed";
            false
      in
    
      if not eq then
        let a2 = reduce load a dep in
        print_endline ("Reduced a: " ^ (show_term a2 0));
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
    let rec infer ?(dep=0) (fill: fill) (load: load) (term: term) : term =
      print_endline ("infer: " ^ (show_term term 0) ^ " at depth " ^ string_of_int dep);
      match term with
      | Var (nam, _) -> 
          print_endline ("Error: Can't infer var: " ^ nam);
          raise (InferenceError ("Can't infer var: " ^ nam))
      | Ref nam ->
          (match load nam with
          | Some loaded ->
              print_endline ("Loaded type for ref " ^ nam ^ ": " ^ (show_term loaded.typ 0));
              loaded.typ
          | None -> 
              print_endline ("Warning: Ref " ^ nam ^ " not found");
              Ref nam)
      | Hol (nam, ctx, cap) -> 
          print_endline ("Infer hole: " ^ nam);
          Hol (nam ^ "_T", ctx, cap)
      | Set -> 
          print_endline "Infer Set";
          Set
      | All (nam, inp, bod) ->
          print_endline ("Infer All: " ^ nam);
          ignore (check fill load inp Set true dep);
          ignore (check fill load (bod (Ann (false, Var (nam, dep), inp))) Set true (dep + 1));
          Set
      | Lam (nam, bod) ->
          print_endline ("Infer Lam: " ^ nam);
          All (nam,
            Hol (nam ^ "_I", Nil, Nil),
            (fun x -> Hol (nam ^ "_O", Cons ((nam, x), Nil), Nil)))
      | App (fun_term, arg_term) ->
          print_endline "Infer App";
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
              print_endline ("Checking App argument: " ^ (show_term arg_term 0));
              ignore (check fill load arg_term inp true dep);
              bod arg_term
          | _ ->
              print_endline ("Error: NonFunApp");
              print_endline ("- fun: " ^ (show_term fun_term dep));
              print_endline ("- typ: " ^ (show_term fun_ty dep));
              raise (InferenceError "NonFunApp"))
      | Fix (nam, typ, bod) ->
          print_endline ("Infer Fix: " ^ nam);
          infer fill load (bod (Ann (false, Var (nam, dep), typ))) ~dep:(dep + 1)
      | Ins val_ ->
          print_endline "Infer Ins";
          let val_ty = reduce load (infer fill load val_ ~dep) dep in
          (match val_ty with
          | Slf (nam, bod) -> bod term
          | _ -> raise (InferenceError "NonSlfIns"))
      | Slf (nam, bod) ->
          print_endline ("Infer Slf: " ^ nam);
          ignore (check fill load (bod (Ann (false, Var (nam, dep), term))) Set true dep);
          Set
      | Ann (chk, val_, typ) ->
          print_endline ("Infer Ann");
          check fill load val_ typ chk dep
      | Let _ -> 
          print_endline ("Error: NonAnnLet");
          raise (InferenceError "NonAnnLet")
      | Def _ -> 
          print_endline ("Error: NonAnnDef");
          raise (InferenceError "NonAnnDef")
    
    (* Assume check exists and has the expected signature *)
  and check (fill: fill) (load: load) (val_: term) (tty: term) (chk: bool) (dep: int) : term =
    print_endline ("check: " ^ (show_term val_ 0) ^ " against type " ^ (show_term tty 0) ^ " at depth " ^ string_of_int dep);
    let typ = reduce load tty dep in
    match chk with 
    | false -> 
      print_endline ("Check: NoCheck");
      typ
    | true -> 
      (match val_ with
      | Lam (nam, bod) ->
          print_endline ("Check Lam: " ^ nam);
          (match typ with
            | All (typ_nam, inp, typ_bod) ->
                ignore (check fill load (bod (Ann (false, Var(nam, dep), inp))) (typ_bod (Ann(false, Var(typ_nam, dep), inp))) chk (dep + 1));
                typ
            | _ ->
                print_endline ("Error: NonFunLam");
                raise (Type_Error "NonFunLam"))
      | Ins val_inner ->
          print_endline "Check Ins";
          (match typ with
            | Slf (nam, bod_typ) ->
                ignore (check fill load val_inner (bod_typ val_) chk dep);
                typ
            | _ ->
                print_endline ("Error: NonSlfIns");
                raise (Type_Error "NonSlfIns"))
      | Hol (nam, ctx, cap) ->
          print_endline ("Check Hole: " ^ nam);
          (* Implement fill_typed_hole here *)
          typ
      | Let (nam, val_inner, bod) ->
          print_endline ("Check Let: " ^ nam);
          let val_typ = infer ~dep fill load val_inner in
          ignore (check fill load (bod (Ann (false, val_inner, val_typ))) typ chk (dep + 1));
          typ
      | Def (nam, val_inner, bod) ->
          print_endline ("Check Def: " ^ nam);
          ignore (check fill load (bod val_inner) typ chk (dep + 1));
          typ
      | _ ->
          print_endline ("Checking other");
          let inf = infer ~dep fill load val_ in
          let inf = reduce load inf dep in
          print_endline ("Check other: " ^ (show_term inf 0) ^ " expected: " ^ (show_term typ 0)); 
          (match (equal (Some fill) load typ inf dep) with
          | true -> typ
          | false ->
              let exp = show_term val_ dep in
              let det = show_term tty dep in
              let msg = "TypeMismatch\n- expected: " ^ exp ^ "\n- detected: " ^ det in
              print_endline msg;
              raise (Type_Mismatch msg)
          ))
  

  let rec replace (rep: term -> term option) (term: term): term =
    match rep term with
    | Some replaced -> replaced
    | None ->
      match term with
      | Var _ | Set | Ref _ -> term
      | All (nam, inp, bod) -> All (nam, replace rep inp, fun x -> replace rep (bod x))
      | Lam (nam, bod) -> Lam (nam, fun x -> replace rep (bod x))
      | App (fun_term, arg_term) -> App (replace rep fun_term, replace rep arg_term)
      | Fix (nam, typ, bod) -> Fix (nam, replace rep typ, fun x -> replace rep (bod x))
      | Slf (nam, bod) -> Slf (nam, fun x -> replace rep (bod x))
      | Ins val_ -> Ins (replace rep val_)
      | Ann (chk, val_, typ) -> Ann (chk, replace rep val_, replace rep typ)
      | Let (nam, val_, bod) -> Let (nam, replace rep val_, fun x -> replace rep (bod x))
      | Def (nam, val_, bod) -> Def (nam, replace rep val_, fun x -> replace rep (bod x))
      | Hol (nam, ctx, cap) -> Hol (nam, ctx, cap)

  let fill_valued_hole fill load nam ctx cap val_ dep = raise Not_Implemented

  let fill_typed_hole (fill: fill) (load: load) (nam: string) (ctx: context) (cap: term list_t) (typ: term) (dep: int): unit =
    raise Not_Implemented

  let rec subst_holes (fill: fill) (term: term) (dep: int): term =
    match term with
    | Var _ | Set | Ref _ -> term
    | All (nam, inp, bod) -> All (nam, subst_holes fill inp dep, fun x -> subst_holes fill (bod x) (dep + 1))
    | Lam (nam, bod) -> Lam (nam, fun x -> subst_holes fill (bod x) dep)
    | App (fun_term, arg_term) -> App (subst_holes fill fun_term dep, subst_holes fill arg_term dep)
    | Fix (nam, typ, bod) -> Fix (nam, subst_holes fill typ dep, fun x -> subst_holes fill (bod x) (dep + 1))
    | Slf (nam, bod) -> Slf (nam, fun x -> subst_holes fill (bod x) dep)
    | Ins val_ -> Ins (subst_holes fill val_ dep)
    | Ann (chk, val_, typ) -> Ann (chk, subst_holes fill val_ dep, subst_holes fill typ dep)
    | Let (nam, val_, bod) -> Let (nam, subst_holes fill val_ dep, fun x -> subst_holes fill (bod x) (dep + 1))
    | Def (nam, val_, bod) -> Def (nam, subst_holes fill val_ dep, fun x -> subst_holes fill (bod x) (dep + 1))
    | Hol (nam, ctx, cap) ->
      match Hashtbl.find_opt fill nam with
      | Some filled ->
        let rec args cap filled =
          match cap with
          | Cons (head, tail) -> args tail (App (filled, head))
          | Nil -> filled
        in
        subst_holes fill (args cap filled) dep
      | None -> term

    (* Syntax *)

  let rec cleanup (term: term) (dep: int): term =
    match term with
    | All (nam, inp, bod) -> All (nam, cleanup inp dep, fun x -> cleanup (bod x) (dep + 1))
    | Lam (nam, bod) -> Lam (nam, fun x -> cleanup (bod x) (dep + 1))
    | App (fun_term, arg_term) -> App (cleanup fun_term dep, cleanup arg_term dep)
    | Fix (nam, typ, bod) -> Fix (nam, cleanup typ dep, fun x -> cleanup (bod x) (dep + 1))
    | Ann (_, val_, _) -> cleanup val_ dep
    | Let (_, val_, bod) -> cleanup (bod val_) dep
    | Def (_, val_, bod) -> cleanup (bod val_) dep
    | _ -> term

  let rec check_def (load: load) (name: string): string =
    try
      match load name with
      | Some loaded ->
        let { val_; typ } = loaded in
        let fill = Hashtbl.create 10 in
        ignore (check fill load val_ typ true 0);
        if Hashtbl.length fill > 0 then
          let new_val = subst_holes fill val_ 0 in
          let new_typ = subst_holes fill typ 0 in
          let new_def = { val_ = new_val; typ = new_typ } in
          let new_load k = if k = name then Some new_def else load k in
          check_def new_load name
        else
          let val_ = cleanup val_ 0 in
          let typ = cleanup typ 0 in
          Printf.printf "\x1b[32m✔ %s\x1b[0m\n" name;
          (* Uncomment to print definitions *)
          Printf.printf "%s\n: %s\n= %s\n" name (show_term typ 0) (show_term val_ 0);
          name ^ "\n: " ^ (show_term typ 0) ^ "\n= " ^ (show_term val_ 0)
      | None -> raise (Failure ("Couldn't load '" ^ name ^ "'."))
    with
    | Stack_overflow ->
      Printf.printf "\x1b[33m? %s\x1b[0m\n" name;
      name ^ "⊥"
    | e ->
      Printf.printf "\x1b[31m✘ %s\x1b[0m\n" name;
      raise e

  let check_book (book: book) =
    Hashtbl.iter (fun name _ -> ignore (check_def (fun k -> Hashtbl.find_opt book k) name)) book

  (* Syntax *)

  let show_ann ann dep =
    match ann with
    | Ann (_, val_, typ) -> show_term val_ dep ^ ": " ^ show_term (normal ~dep (fun _ -> None) typ) dep
    | _ -> show_term ann dep

  let show_def name val_ typ =
    let rec show_typ term dep =
      let tab = if dep = 0 then "\n: " else "\n  " in
      match term with
      | All (nam, inp, bod) -> tab ^ "∀(" ^ nam ^ ": " ^ show_term inp dep ^ ") " ^ show_typ (bod (Var (nam, dep))) (dep + 1)
      | _ -> tab ^ show_term term dep
    in
    let rec show_val term dep =
      match term with
      | Lam (nam, bod) -> "λ" ^ nam ^ " " ^ show_val (bod (Var (nam, dep))) (dep + 1)
      | _ -> if dep > 0 then "\n  " else "" ^ show_term term dep
    in
    name ^ show_typ typ 0 ^ "\n= " ^ show_val val_ 0

  let show_book book =
    let text = ref "" in
    Hashtbl.iter (fun name { typ; val_ } -> text := !text ^ show_def name val_ typ) book;
    !text

    let num_to_str num =
      let rec aux num txt =
        if num > 0 then
          let char_code = ((num - 1) mod 26) + Char.code 'a' in
          let new_char = Char.chr char_code in
          aux ((num - 1) / 26) (String.make 1 new_char ^ txt)
        else
          txt
      in
      aux (num + 1) ""

  let rec find list nam =
    match list with
    | Cons ((name, term), tail) -> if name = nam then term else find tail nam
    | Nil -> Ref nam

  let rec gets list idx =
    match list with
    | Cons ((_, term), tail) -> if idx = 0 then term else gets tail (idx - 1)
    | Nil -> failwith "unbound"

  (* OCaml equivalent of the TypeScript skip function *)
let rec skip code =
  let rec drop_while predicate s =
    if String.length s > 0 && predicate (String.get s 0) then
      drop_while predicate (String.sub s 1 ((String.length s) - 1))
    else
      s
  in
  if String.length code >= 2 && String.sub code 0 2 = "//" then
    skip (drop_while (fun c -> c <> '\n') code)
  else if String.length code > 0 && (String.get code 0 = '\n' || String.get code 0 = ' ') then
    skip (String.sub code 1 ((String.length code) - 1))
  else
    code

(* OCaml equivalent of the TypeScript is_name_char function *)
let is_name_char c =
  let regex = Str.regexp "[a-zA-Z0-9_]" in
  Str.string_match regex (String.make 1 c) 0

(* OCaml equivalent of the TypeScript parse_name function *)
let parse_name code =
  let code' = ref (skip code) in
  let name = ref "" in
  while (is_name_char (String.get !code' 0)) do
    name := !name ^ (String.make 1 (String.get !code' 0));
    code' := String.sub !code' 1 ((String.length !code') - 1)
  done;
  (!code', !name)
  
let rec parse_text code text =
  let code = skip code in
  if String.length text = 0 then
    code, ()
  else if code.[0] = text.[0] then
    parse_text(String.sub code 1 ((String.length code) - 1)) (String.sub text 1 ((String.length text) - 1))
  else
    raise (ParseError ("Expected '" ^ text ^ "'"))

let rec parse_term code =
  let code = skip code in
  if String.length code = 0 then raise (ParseError "Unexpected end of input");

  let first_two_chars = if String.length code >= 2 then String.sub code 0 2 else "" in
  let first_three_chars = if String.length code >= 3 then String.sub code 0 3 else "" in
  match first_three_chars, first_two_chars with
  | "\u{2200}", _ -> (* ∀ - Forall *)
      let code = String.sub code 3 (String.length code - 3) in
      let code, _ = parse_text code "(" in
      let code, nam = parse_name code in
      let code, _ = parse_text code ":" in
      let code, typ = parse_term code in
      let code, _ = parse_text code ")" in
      let code, bod = parse_term code in
      (code, fun ctx -> All (nam, typ ctx, fun x -> bod (Cons ((nam, x), ctx))))
  | _, "\u{03BB}" -> (* λ - Lambda *)
      let code = String.sub code 2 (String.length code - 2) in
      let code, nam = parse_name code in
      let code, bod = parse_term code in
      (code, fun ctx -> Lam (nam, fun x -> bod (Cons ((nam, x), ctx))))
  | _, "\u{03BC}" -> (* μ - Mu *)
      let code = String.sub code 2 (String.length code - 2) in
      let code, nam = parse_name code in
      let code, _ = parse_text code ":" in
      let code, typ = parse_term code in
      let code, _ = parse_text code ")" in
      let code, bod = parse_term code in
      (code, fun ctx -> Fix (nam, typ ctx, fun x -> bod (Cons ((nam, x), ctx))))
  | _, t -> parse_non_unicode_terms code

and parse_non_unicode_terms code =
    (* print_endline (String.sub code 0 1); *)
    match String.get code 0 with
  | '(' ->
      let code, fun_ = parse_term (String.sub code 1 (String.length code - 1)) in
      let rec parse_args code args =
        let code = skip code in
        if String.length code = 0 || code.[0] = ')' then (code, List.rev args)
        else
          let code, arg = parse_term code in
          parse_args code (arg :: args)
      in
      let code, args = parse_args code [] in
      let code, _ = parse_text code ")" in
      (code, fun ctx -> List.fold_left (fun f x -> App (f, x ctx)) (fun_ ctx) args)
  | '*' ->
      (String.sub code 1 (String.length code - 1), fun _ -> Set)
  | '$' ->
      let code, nam = parse_name (String.sub code 1 (String.length code - 1)) in
      let code, bod = parse_term code in
      (code, fun ctx -> Slf (nam, fun x -> bod (Cons ((nam, x), ctx))))
  | '~' ->
      let code, val_ = parse_term (String.sub code 1 (String.length code - 1)) in
      (code, fun ctx -> Ins (val_ ctx))
  | '{' ->
      let code, val_ = parse_term (String.sub code 1 (String.length code - 1)) in
      let code, _ = parse_text code ":" in
      let code, typ = parse_term code in
      let code, _ = parse_text code "}" in
      (code, fun ctx -> Ann (true, val_ ctx, typ ctx))
  | 'l' when String.sub code 0 4 = "let " ->
      let code, nam = parse_name (String.sub code 4 (String.length code - 4)) in
      let code, _ = parse_text code "=" in
      let code, val_ = parse_term code in
      let code, bod = parse_term code in
      (code, fun ctx -> Let (nam, val_ ctx, fun x -> bod (Cons ((nam, x), ctx))))
  | 'd' when String.sub code 0 4 = "def " ->
      let code, nam = parse_name (String.sub code 4 (String.length code - 4)) in
      let code, _ = parse_text code "=" in
      let code, val_ = parse_term code in
      let code, bod = parse_term code in
      (code, fun ctx -> Def (nam, val_ ctx, fun x -> bod (Cons ((nam, x), ctx))))
  | '?' ->
      let code, nam = parse_name (String.sub code 1 (String.length code - 1)) in
      (code, fun ctx -> Hol ("?" ^ nam, ctx, Nil))
  | '%' ->
      let code, idx = parse_name (String.sub code 1 (String.length code - 1)) in
      (code, fun ctx -> gets ctx (int_of_string idx))
  | _ ->
      let code, nam = parse_name code in
      if nam = "" then raise (ParseError "Expected a variable name")
      else (code, fun ctx -> find ctx nam)

  let do_parse_term code = snd (parse_term code) Nil

  let parse_def code =
    let code, nam = parse_name (skip code) in
    let code, _ = parse_text code ":" in
    let code, typ = parse_term code in
    let code, _ = parse_text code "=" in
    let code, val_ = parse_term code in
    code, nam, { typ = typ Nil; val_ = val_ Nil }

  let parse_book code =
    let book = Hashtbl.create 10 in
    let rec aux code =
      if String.length code > 0 then
        let code, nam, def = parse_def code in
        Hashtbl.add book nam def;
        aux (skip code)
    in
    aux code;
    book

  let do_parse_book code = parse_book code

  let loader book =
    fun name ->
      if not (Hashtbl.mem book name) then
        try
          let ic = open_in (name ^ ".tl") in
          let code = really_input_string ic (in_channel_length ic) in
          close_in ic;
          let book_defs = parse_book code in
          Hashtbl.iter (fun k v -> Hashtbl.add book k v) book_defs;
          if Hashtbl.mem book name then 
            Some (Hashtbl.find book name)
          else
            None
        with
        | Sys_error _ -> None
        | _ -> None
      else
        Some (Hashtbl.find book name)
  
  
end