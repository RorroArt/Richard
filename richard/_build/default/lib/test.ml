open Lang

let equal_def = {
  typ = Lang.All ("A", Lang.Set, fun A ->
          Lang.All ("a", Lang.Var ("A", 0), fun a ->
          Lang.All ("b", Lang.Var ("A", 0), fun b ->
          Lang.Set)));
  val_ = Lang.Lam ("A", fun A ->
          Lang.Lam ("a", fun a ->
          Lang.Lam ("b", fun b ->
          Lang.All ("P", Lang.All ("x", Lang.Var ("A", 0), Lang.Set), fun P ->
          Lang.All ("p", Lang.App (Lang.Var ("P", 0), Lang.Var ("a", 0)), fun p ->
          Lang.App (Lang.Var ("P", 0), Lang.Var ("b", 0)))))))
}



let nat_def = {
  typ = Lang.Set;
  val_ = Lang.Slf ("self", fun self ->
          Lang.All ("P", Lang.All ("n", Lang.Ref "Nat", Lang.Set), fun P ->
          Lang.All ("s", Lang.All ("n", Lang.Ref "Nat", Lang.App (Lang.Var ("P", 0), Lang.App (Lang.Var ("succ", 0), Lang.Var ("n", 0)))), fun s ->
          Lang.All ("z", Lang.App (Lang.Var ("P", 0), Lang.Ref "zero"), fun z ->
          Lang.App (Lang.Var ("P", 0), Lang.Var ("self", 0))))))
}


let test_equal_check () =
  let fill = Hashtbl.create 10 in
  let load _ = None in
  try
    let _ = Lang.check fill load equal_def.val_ equal_def.typ true 0 in
    print_endline "Equal type check passed"
  with Lang.Type_Error msg ->
    print_endline ("Equal type check failed: " ^ msg)


let test_cong_check () =
  let fill = Hashtbl.create 10 in
  let load name =
    match name with
    | "Equal" -> Some equal_def
    | _ -> None
  in
  try
    let _ = Lang.check fill load cong_def.val_ cong_def.typ true 0 in
    print_endline "cong type check passed"
  with Lang.Type_Error msg ->
    print_endline ("cong type check failed: " ^ msg)


let test_equal_infer () =
  let fill = Hashtbl.create 10 in
  let load _ = None in
  try
    let inferred_type = Lang.infer fill load equal_def.val_ in
    if Lang.equal None load inferred_type equal_def.typ 0 then
      print_endline "Equal type inference passed"
    else
      print_endline "Equal type inference failed: inferred type does not match expected type"
  with Lang.InferenceError msg ->
    print_endline ("Equal type inference failed: " ^ msg)

let test_cong_infer () =
  let fill = Hashtbl.create 10 in
  let load name =
    match name with
    | "Equal" -> Some equal_def
    | _ -> None
  in
  try
    let inferred_type = Lang.infer fill load cong_def.val_ in
    if Lang.equal None load inferred_type cong_def.typ 0 then
      print_endline "cong type inference passed"
    else
      print_endline "cong type inference failed: inferred type does not match expected type"
  with Lang.InferenceError msg ->
    print_endline ("cong type inference failed: " ^ msg)

let test_cong_reduce () =
  let load name =
    match name with
    | "Equal" -> Some equal_def
    | _ -> None
  in
  let reduced_term = Lang.reduce load cong_def.val_ 0 in
  if Lang.equal None load reduced_term cong_def.val_ 0 then
    print_endline "cong reduction passed"
  else
    print_endline "cong reduction failed: reduced term does not match original term"

let () =
  test_equal_check ();
  test_cong_check ();
  test_equal_infer ();
  test_cong_infer ();
  test_equal_reduce ();
  test_cong_reduce ()
