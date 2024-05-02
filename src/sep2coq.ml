open Gospel
open Sep_ast
open Coq
open Formula
open Ttypes
open Symbols
open Coq_driver
module M = Map.Make (String)

let to_triple s = "_" ^ s ^ "_spec"

let ty_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty type_mapping_list

let id_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty id_mapping_list

let is_ignore x =
  List.mem x ignore_list

let mk_qualid name path =
  List.fold_right (fun s1 s2 -> s1 ^ "." ^ s2) path name

let map_sym map id =
  match id.Ident.id_path with
  |"Gospelstdlib"::t | "#Base_lang"::t  ->
    let qualid = mk_qualid id.id_str t in
    begin try M.find qualid map with
    |Not_found -> id.id_str end
  |_ -> id.id_str

let map_id id =
  map_sym id_map id

let map_ty v =
  map_sym ty_map v.ts_ident

let to_type = String.capitalize_ascii

let var_of_ty ?(b2p=true) t =
  let rec var_of_ty t = 
    let coq_var x = coq_var (map_ty x) in
    match t.ty_node with
    | Tyapp (v, _) when ts_equal v ts_loc -> coq_var v
    | Tyapp (v, [t1; t2]) when ts_equal v ts_arrow ->
       coq_impl (var_of_ty t1) (var_of_ty t2)
    | Tyapp(v, []) when b2p && ts_equal v ts_bool ->
       coq_typ_prop
    | Tyapp (v, l) -> coq_apps (coq_var v) (List.map var_of_ty l)
    | Tyvar tv -> Coq_var (to_type tv.tv_name.id_str) in
  var_of_ty t

exception WIP

let coq_id id = coq_var (map_id id)
let gen_args vs = (vs.vs_name.id_str, var_of_ty ~b2p:false vs.vs_ty)

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

let var_of_pat p = match p.Tterm.p_node with
  |Pvar vs -> vs.vs_name.id_str, (var_of_ty vs.vs_ty)
  |Pwild -> "_", var_of_ty p.p_ty
  |_ -> assert false

let coq_const c =
  match c with
  | Ppxlib.Pconst_integer (v, _) -> coq_int (int_of_string v)
  | _ -> assert false

let rec get_aliases p = match p.Tterm.p_node with
  | Pwild | Papp _ -> []
  | Pvar vs -> [coq_id vs.vs_name]
  | Pas (p1, v) -> (coq_id v.vs_name) :: (get_aliases p1)
  | Por _ | Pconst _ | Pinterval _-> assert false

let rec case (p, _, t) = coq_pattern p, coq_term t
and bool_case al p t =
  let t = coq_term t in
  let eq_true x = coq_apps (Coq_var "Coq.Init.Logic.eq") [coq_bool_true; x] in
  coq_pattern p, Coq_lettuple(al, coq_tuple (List.map eq_true al), t)

and to_prop_case t l =
  let bop = coq_var "Gospel.bool_of_prop" in
  let t = coq_app bop t in
  let branches =
    List.map (fun (p, g, t) ->
        let al = get_aliases p in
        if al = [] then case (p, g, t) else bool_case al p t) l in 
  coq_match t branches

and coq_term t =
  match t.Tterm.t_node with
  | Tvar v -> coq_id v.vs_name
  | Tconst c -> coq_const c
  | Tapp (f, [t]) when
         is_ignore (mk_qualid f.ls_name.id_str f.ls_name.id_path) ->
     coq_term t
  | Tapp (f, [t1; t2])
       when f.ls_name.id_str = "apply" ->
     coq_app (coq_term t1) (coq_term t2)
  | Tapp (f, [t1; t2])
       when f.ls_name.id_str = "remove"
            && f.ls_name.id_path = ["Gospelstdlib"; "Set"] ->
     let singleton_set = coq_var "TLC.LibSet.single_impl" in
     let set = coq_app singleton_set (coq_term t1) in
     let var = coq_id f.ls_name in
     coq_apps var [coq_term t2; set]
  | Tapp (f, t1::t) when
         ls_equal f ps_equ &&
           ty_equal t1.t_ty ty_bool ->
     let ct1 = coq_term t1 in
     let arg_maybe = List.map coq_term t in 
     coq_apps (coq_var "Coq.Init.Logic.iff") (ct1::arg_maybe)
  | Tapp (f, []) when (ls_equal f fs_bool_true)  ->
     coq_prop_true
  | Tapp (f, []) when (ls_equal f fs_bool_false)  ->
     coq_prop_false
  | Tapp (f, args) ->
     let var = coq_id f.ls_name in
     coq_apps var (List.map coq_term args)
  | Tfield _ -> assert false
  | Tif(g, th, el) ->
     let gc = coq_term g in
     let thc = coq_term th in
     let elc = coq_term el in
     coq_if_prop gc thc elc
  | Tcase (t, l) ->
     let e = (coq_term t) in 
     if ty_equal t.t_ty ty_bool then
       to_prop_case e l
     else
       coq_match e (List.map case l)
  | Tquant(q, ids, t) ->
     let f = match q with |Tforall -> coq_foralls |Texists -> coq_exists in
     let ids = List.map gen_args ids in
     f ids (coq_term t)
  | Tlambda(vl, t) ->
     coq_funs (List.map var_of_pat vl) (coq_term t)
  | Tlet (vs, t1, t2) ->
     let id = coq_id vs.vs_name in
     Coq_lettuple([id], coq_term t1, coq_term t2)
  | Tbinop (b, t1, t2) -> 
      let ct1 = coq_term t1 in
      let ct2 = coq_term t2 in
      begin match b with
      | Tand | Tand_asym -> coq_app_conj ct1 ct2
      | Tor | Tor_asym -> coq_app_disj ct1 ct2
      | Timplies -> Coq_impl (ct1, ct2)
      | Tiff -> coq_apps (coq_var "Coq.Init.Logic.iff") [ct1; ct2] end
  | Tnot t -> coq_app coq_not (coq_term t)
  | Told t -> coq_term t

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
          (List.map (fun v -> (v.vs_name.id_str, var_of_ty ~b2p:false v.vs_ty)) args, b)
      | b -> ([ ("_", coq_typ_unit) ], b)
    in
    coq_funs args (cfml_term body)
  in
  let triple = coq_apps_var "CFML.SepLifted.Triple" [ trm; pre; post ] in
  coq_foralls all_vars triple

let mk_enc = (^) "_E"

let get_poly args =
  let rec get_poly ty = match ty.ty_node with
    |Tyvar v -> [v.tv_name.id_str]
    |Tyapp (_, l) -> List.concat_map get_poly l in
  List.concat_map (fun v -> get_poly v.vs_ty) args
  |> List.sort_uniq compare

let sep_def d =
  match d.d_node with
  | Type (id, _) -> [
      Coqtop_param (id.id_str, Coq_type);
      Coqtop_context [mk_enc id.id_str, enc_type  (coq_var id.id_str)]
    ]
  | Pred (id, args) ->
     let args = List.rev args in
     let poly = get_poly args in
     let types = List.map (fun v -> var_of_ty v.vs_ty) args in
     let t = coq_impls types hprop in
     let typed_var v = "{" ^ String.capitalize_ascii v, Coq_var "Type}" in
     let with_poly = coq_foralls (List.map typed_var poly) t in
     [ Coqtop_param (id.id_str, with_poly) ]
  | Triple triple ->
     let fun_def = triple.triple_name.id_str, Formula.func_type in
     let fun_triple = gen_spec triple in
     let triple_name = to_triple triple.triple_name.id_str in
     coqtop_params [ fun_def; (triple_name, fun_triple) ]
  | Function f ->
     let name = f.fun_ls.ls_name.id_str in
     let args = f.fun_params in
     let ret = f.fun_ls.ls_value in
     let ret_coq = var_of_ty ret in 
     let args_coq = List.map (fun arg -> arg.vs_name.id_str, var_of_ty arg.vs_ty) args in
     let def = Option.map coq_term f.fun_def in
     begin match def with
     |Some d -> 
       let coq_def = name, args_coq, ret_coq, d in 
       if f.fun_rec then
         [coqtop_fixdef coq_def]
       else
         [coqtop_fundef coq_def]
     |None -> coqtop_params [name, coq_impls (List.map snd args_coq) ret_coq] end
  | Axiom a ->
     coqtop_params [a.ax_name.id_str, coq_term a.ax_term]

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
        [ "Coq.ZArith.BinIntDef"; "CFML.Semantics"; "CFML.WPHeader";
        ];
      Coqtop_custom "Delimit Scope Z_scope with Z."
      (*Coqtop_custom "Existing Instance WPHeader.Enc_any | 99."*);
    ]
  in

  imports @ List.concat_map sep_def l
