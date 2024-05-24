open Richard
open Notty
open Notty_unix
open Lang
open Printf

let book : Lang.book = Hashtbl.create 100

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


(* let book : Lang.book = Hashtbl.create 10

let load_book path =
  try
    let ic = open_in path in
    let code = really_input_string ic (in_channel_length ic) in
    close_in ic;
    let new_book = Lang.do_parse_book code in
    Hashtbl.iter (fun k v -> Hashtbl.replace book k v) new_book;
    Some new_book
  with
  | _ -> None

let draw_interface left_content right_content command_buffer =
  let left_pane = I.string A.(fg lightblue) left_content in
  let right_pane = I.string A.(fg lightgreen) right_content in
  let screen_height = max (I.height left_pane) (I.height right_pane) in
  let vertical_divider = I.char A.(fg lightred) '|' 1 screen_height in
  let left_pane_full_height = I.vsnap ~align:`Top screen_height left_pane in
  let right_pane_full_height = I.vsnap ~align:`Top screen_height right_pane in
  let command_pane = I.string A.(fg white) command_buffer in
  let horizontal_divider = I.char A.(fg lightred) '-' (I.width left_pane_full_height + 1 + I.width right_pane_full_height) 1 in
  let main_pane = I.hcat [
    left_pane_full_height;
    vertical_divider;
    right_pane_full_height
  ] in
  I.vcat [
    main_pane;
    horizontal_divider;
    command_pane
  ]

let rec editor term content cursor =
  Term.image term (I.string A.empty content);
  match Term.event term with
  | `Key (`Escape, _) -> content
  | `Key (`Enter, _) ->
    let new_content = content ^ "\n" in
    editor term new_content (cursor + 1)
  | `Key (`Backspace, _) ->
    let new_content = if String.length content > 0 then String.sub content 0 (String.length content - 1) else content in
    editor term new_content (cursor - 1)
  | `Key (`ASCII c, _) ->
    let new_content = content ^ (String.make 1 c) in
    editor term new_content (cursor + 1)
  | _ -> editor term content cursor

let get_proof_goal script =
  try
    let goal = "Proof Goal based on the script: " ^ script in
    goal
  with
  | _ -> "Error in generating proof goal"

let rec command_buffer term left_content right_content command =
  let update_interface = draw_interface left_content right_content command in
  Term.image term update_interface;
  match Term.event term with
  | `Key (`Escape, _) -> event_loop term left_content right_content ""
  | `Key (`Enter, _) ->
    (match command with
     | ":q" -> ()
     | ":n" ->
       let normalized_script = Lang.show_term (Lang.normal (fun _ -> None) (Lang.do_parse_term left_content)) 0 in
       event_loop term normalized_script right_content ""
     | ":c" ->
       let checked_code = Lang.check_def (fun k -> Hashtbl.find_opt book k) left_content in
       event_loop term left_content ("Checked: " ^ checked_code) ""
     | cmd when String.length cmd > 3 && String.sub cmd 0 3 = ":e " ->
       let path = String.sub cmd 3 (String.length cmd - 3) in
       (match load_book path with
        | Some _ -> event_loop term left_content "Book loaded successfully" ""
        | None -> event_loop term left_content "Failed to load book" "")
     | _ -> event_loop term left_content right_content "")
  | `Key (`Backspace, _) ->
    let new_command = if String.length command > 0 then String.sub command 0 (String.length command - 1) else command in
    command_buffer term left_content right_content new_command
  | `Key (`ASCII c, _) ->
    let new_command = command ^ (String.make 1 c) in
    command_buffer term left_content right_content new_command
  | _ -> command_buffer term left_content right_content command

and event_loop term left_content right_content cmd_buffer =
  Term.image term (draw_interface left_content right_content cmd_buffer);
  match Term.event term with
  | `Key (`Escape, _) -> ()
  | `Key (`ASCII 'q', _) -> ()
  | `Key (`ASCII ':', _) ->
    command_buffer term left_content right_content ":"
  | `Key (`ASCII 'e', _) ->
    let new_left_content = editor term left_content 0 in
    event_loop term new_left_content right_content cmd_buffer
  | `Resize (w, h) -> event_loop term left_content right_content cmd_buffer
  | _ -> event_loop term left_content right_content cmd_buffer

let () =
  let term = Term.create () in
  let left_content = "Left Pane: Proof Script" in
  let right_content = "Right Pane: Proof State and Goals" in
  let command_buffer = "" in
  try event_loop term left_content right_content command_buffer
  with exn -> Term.release term; raise exn *)
