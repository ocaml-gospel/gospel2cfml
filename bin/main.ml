open Gospel2cfml
open Gospel
open Tmodule
open Format

let fname = ref None
let version = "0.1~dev"

let spec =
  [
    ( "--version",
      Arg.Unit
        (fun () ->
          printf "gospel2cfml %s@." version;
          exit 0),
      " print version information" );
  ]

let usage_msg = sprintf "%s <file>.ml\nVerify OCaml program\n" Sys.argv.(0)

let usage () =
  Arg.usage spec usage_msg;
  exit 1

let set_file f =
  match !fname with
  | None when Filename.check_suffix f ".mli" -> fname := Some f
  | _ -> usage ()

let () = Arg.parse spec set_file usage_msg
let fname = match !fname with None -> usage () | Some f -> f

let path2module p =
  Filename.basename p |> Filename.chop_extension |> String.capitalize_ascii

let base_fname f = Filename.basename f |> Filename.chop_extension

let type_check load_path name sigs =
  let md = init_muc name in
  let mn = path2module name in
  let penv =
     Utils.Sstr.singleton mn |> Typing.penv load_path
  in
  let md = List.fold_left (Typing.type_sig_item [mn] penv) md sigs in
  wrap_up_muc md

let () =
  let open Parser_frontend in
  let load_path = [ Filename.dirname fname ] in
  let ocaml = parse_ocaml fname in
  let module_nm = path2module fname in
  let sigs = parse_gospel ~filename:fname ocaml module_nm in
  let file = type_check load_path fname sigs in
  let file_sep = Tast2sep.process_sigs file in
  let file_cfml = Sep2coq.sep_defs file_sep in
  let out_fname = base_fname fname ^ "_mli.v" in
  let directory = "../cfml2/examples/translations/" ^ (String.capitalize_ascii (base_fname fname)) ^ "/" ^ out_fname in
  let fmt = formatter_of_out_channel (open_out directory) in
  fprintf fmt "%s@." (Print_coq.tops file_cfml)

