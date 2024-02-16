open Gospel
open Sep_ast
open Coq
open Formula
open Ttypes
open Symbols
module M = Map.Make (String)

let to_triple s = "_" ^ s ^ "_spec"
let some = "Coq.Init.Datatypes.Some"
let none = "Coq.Init.Datatypes.None"
let nil = "Coq.Lists.List.nil"
let cons = "Coq.Lists.List.cons"
let list = "Coq.Lists.List.list"
let option = "Coq.Init.Datatypes.option"
let length = "LibListZ.length"
let head = "Gospel.hd_gospel"
let tl = "Gospel.tl_gospel"
let eq = "Coq.Init.Logic.eq"
let app = "Coq.Lists.List.app"
let update = "Gospel.update"
let singleton = "Gospel.singleton"

let type_mapping_list = [ ("sequence", list); ("option", option) ]


let id_mapping_list =
  [
    ("Some", some);
    ("None", none);
    ("empty", nil);
    ("cons", cons);
    ("hd", head);
    ("infix =", eq);
    ("infix ++", app);
    ("length", length);
    ("mixfix [->]", update);
    ("tl", tl);
    ("singleton", singleton);
  ]

let ty_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty type_mapping_list

let id_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty id_mapping_list

let map_ty v = try M.find v ty_map with Not_found -> v
let map_id v = try M.find v id_map with Not_found -> v

let rec var_of_ty t =
  let coq_var x = coq_var (map_ty x) in
  match t.ty_node with
  | Tyapp (v, _) when ts_equal v ts_loc -> coq_var v.ts_ident.id_str
  | Tyapp (v, [t1; t2]) when ts_equal v ts_arrow ->
     coq_impl (var_of_ty t1) (var_of_ty t2)
  | Tyapp (v, l) -> coq_apps (coq_var v.ts_ident.id_str) (List.map var_of_ty l)
  | _ -> assert false

exception WIP

let coq_id id = coq_var (map_id id.Ident.id_str)
let gen_args vs = (vs.vs_name.id_str, var_of_ty vs.vs_ty)

let gen_args_opt arg =
  match arg with
  | None -> ((match coq_tt with Coq_var v -> v | _ -> assert false), val_type)
  | Some vs -> gen_args vs

let rec coq_pattern p =
  match p.Tterm.p_node with
  | Pwild -> Coq_wild
  | Pvar vs -> coq_id vs.vs_name
  | Papp (ls, l) -> coq_apps (coq_id ls.ls_name) (List.map coq_pattern l)
  | Por _ | Pas _ | Pinterval _ | Pconst _ -> assert false

let coq_const c =
  match c with
  | Ppxlib.Pconst_integer (v, _) -> coq_int (int_of_string v)
  | _ -> assert false

let rec coq_term t =
  match t.Tterm.t_node with
  | Tvar v -> coq_id v.vs_name
  | Tconst c -> coq_const c
  | Tapp (f, [t]) when
         f.ls_name.id_str = "integer_of_int" ||
           f.ls_name.id_str = "to_seq" ->
     coq_term t
  | Tapp (f, [t1; t2])
       when f.ls_name.id_str = "apply" ->
     coq_app (coq_term t1) (coq_term t2)
  | Tapp (f, args) ->
     let var = coq_id f.ls_name in
     coq_apps var (List.map coq_term args)
  | Tfield _ -> assert false
  | Tif _ -> assert false
  | Tcase (t, l) ->
      let case (p, _, t) = (coq_pattern p, coq_term t) in
      coq_match (coq_term t) (List.map case l)
  | Tquant(q, ids, t) ->
     let f = match q with |Tforall -> coq_foralls |Texists -> coq_exists in
     let ids = List.map gen_args ids in
     f ids (coq_term t)
  | Tlambda _ -> assert false
  | Tlet (vs, t1, t2) ->
     let id = coq_id vs.vs_name in
     Coq_lettuple([id], coq_term t1, coq_term t2)
  | Tbinop (b, t1, t2) -> (
      let ct1 = coq_term t1 in
      let ct2 = coq_term t2 in
      match b with
      | Tand | Tand_asym -> coq_app_conj ct1 ct2
      | Tor | Tor_asym -> coq_app_disj ct1 ct2
      | Timplies -> Coq_impl (ct1, ct2)
      | Tiff -> coq_impl ct1 ct2)
  | Tnot t -> coq_app coq_not (coq_term t)
  | Told t -> coq_term t
  | Ttrue -> coq_prop_true
  | Tfalse -> coq_prop_false

let rec cfml_term = function
  | Star l -> hstars (List.map cfml_term l)
  | Pure t -> hpure (coq_term t)
  | App (sym, l) ->
      let loc = List.hd l in
      let rep = List.nth l (List.length l - 1) in
      hdata (coq_id loc.vs_name)
        (coq_app (coq_id sym.ls_name) (coq_id rep.vs_name))
  | Exists (l, term) ->
      let coq_term = cfml_term term in
      List.fold_right
        (fun v acc -> hexists v.vs_name.id_str (var_of_ty v.vs_ty) acc)
        l coq_term
  | _ -> assert false

let gen_spec triple =
  let args = List.map gen_args_opt triple.triple_args in
  let all_vars = List.map gen_args triple.triple_vars in
  let dynargs = List.map (fun (x, t) -> coq_dyn_of t (coq_var x)) args in
  let trm = trm_apps_lifted (coq_var triple.triple_name.id_str) dynargs in
  let pre = cfml_term triple.triple_pre in
  let post =
    let args, body =
      match triple.triple_post with
      | Lambda (args, b) ->
          (List.map (fun v -> (v.vs_name.id_str, var_of_ty v.vs_ty)) args, b)
      | b -> ([ ("__UNUSED__", coq_typ_unit) ], b)
    in
    coq_funs args (cfml_term body)
  in
  let triple = coq_apps_var "CFML.SepLifted.Triple" [ trm; pre; post ] in
  coq_foralls all_vars triple

let sep_def d =
  match d.d_node with
  | Type (id, m, _) -> if m then [] else [ Coqtop_param (id.id_str, Coq_type) ]
  | Pred (id, args) ->
      let args = List.rev args in
      let types = List.map (fun v -> var_of_ty v.vs_ty) args in
      let t = coq_impls types hprop in
      [ Coqtop_param (id.id_str, t) ]
  | Triple triple ->
      let fun_def = (triple.triple_name.id_str, Formula.func_type) in
      let fun_triple = gen_spec triple in
      let triple_name = to_triple triple.triple_name.id_str in
      coqtop_params [ fun_def; (triple_name, fun_triple) ]
  | _ -> []

let sep_defs l =
  let cfml = List.map (fun s -> "CFML." ^ s) in
  let imports =
    [
      Coqtop_set_implicit_args;
      Coqtop_require_import [ "Gospel" ];
      Coqtop_require
        [
          "Coq.ZArith.BinInt";
          "TLC.LibLogic";
          "TLC.LibRelation";
          "TLC.LibInt";
          "TLC.LibListZ";
        ];
      Coqtop_require_import
        (cfml
           [
             "SepBase";
             "SepLifted";
             "WPLib";
             "WPLifted";
             "WPRecord";
             "WPArray";
             "WPBuiltin";
           ]);
      (*coqtop_require_unless no_mystd_include*)
      Coqtop_require
        (cfml [ "Stdlib.Array_ml"; "Stdlib.List_ml"; "Stdlib.Sys_ml" ]);
      Coqtop_require_import
        [ "Coq.ZArith.BinIntDef"; "CFML.Semantics"; "CFML.WPHeader" ];
      Coqtop_custom "Delimit Scope Z_scope with Z."
      (*Coqtop_custom "Existing Instance WPHeader.Enc_any | 99."*);
    ]
  in

  imports @ List.concat_map sep_def l
