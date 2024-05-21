open Richard
open Lang
open Printf

let book : Lang.book = Hashtbl.create 10

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | _ :: func :: name :: _ ->
      let load = Lang.loader book in
      begin match func with
      | "check" ->
          let new_code = Lang.check_def load name in
          if new_code <> "⊥" then
            let oc = open_out (name) in
            output_string oc new_code;
            close_out oc
      | "normalize" ->
          begin match load name with
          | Some def ->
              let normalized = Lang.normal load def.val_ in
              print_endline (Lang.show_term normalized 0)
          | None -> eprintf "Error: Definition '%s' not found.\n" name
          end
      | _ ->
          eprintf "Usage: richard [check|normalize] <name>\n"
      end
  | _ -> eprintf "Usage: richard [check|normalize] <name>\n"
