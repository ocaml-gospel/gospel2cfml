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

let id_mapper = function
  |"prefix -" -> "neg"
  |"infix +" -> "plus"
  |"infix -" -> "minus"
  |"infix *" -> "mult"
  |"infix /" -> "div"
  |"infix >" -> "gt"
  |"infix >=" -> "ge"
  |"infix <" -> "lt"
  |"infix <=" -> "le"
  |"infix ++" -> "app"
  |"mixfix [_]" -> "seq_get"
  |"mixfix [_.._]" -> "seq_sub"
  |"mixfix [_..]" -> "seq_sub_l"
  |"mixfix [.._]" -> "seq_sub_r"
  |"mixfix [->]" -> "map_set"
  |"mixfix {}" -> "set_create"
  |"prefix !" -> "_UNUSED"
  |s -> s

let coq_keywords = ["mod"; "Set"; "Alias"]

let valid_coq_id s =
  if List.mem s coq_keywords
  then "_" ^ s
  else id_mapper s

let qual_var qual id =
  List.fold_left (fun acc x -> (valid_coq_id x) ^ "." ^ acc) (valid_coq_id id) qual
  
let map_sym map qual id =
  match id.Ident.id_path with
  (*| "Gospelstdlib"::t *)  | "#Base_lang"::t  ->
                              let qualid = mk_qualid id.id_str t in
                              begin try M.find qualid map with
                                    |Not_found -> id.id_str end
  |_ -> qual_var qual id.id_str

let map_id qual id =
  map_sym id_map qual id

let map_ty v =
  map_sym ty_map [] v.ts_ident

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
    | Tyvar tv ->
       Coq_var tv.tv_name.id_str in
  var_of_ty t

exception WIP

let coq_id ?(qual=[]) id = coq_var (map_id qual id)
let gen_args vs = tv vs.vs_name.id_str (var_of_ty ~b2p:false vs.vs_ty) false

let gen_args_opt vs =
  if vs.vs_name.id_str = "()" then 
     let v = match coq_tt with Coq_var v -> v | _ -> assert false in
     tv v val_type false else
    gen_args vs

let rec coq_pattern p =
  match p.Tterm.p_node with
  | Pwild -> Coq_wild 
  | Pvar vs -> coq_id vs.vs_name
  | Papp (ls, l) -> coq_apps (coq_id ls.ls_name) (List.map coq_pattern l)
  | Por _ | Pas _ | Pinterval _ | Pconst _ -> assert false

let var_of_pat p = match p.Tterm.p_node with
  | Pvar vs -> tv vs.vs_name.id_str (var_of_ty vs.vs_ty) false
  | Pwild -> tv "_" (var_of_ty p.p_ty) false
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

let gen_poly poly_vars =
  let types = List.map (fun v -> tv v.tv_name.id_str Coq_type false) poly_vars in
  let inhab = coq_var "Inhab" in
  let inhab_h =
    List.map (fun v -> tv (v.var_name ^ "Ih") (coq_app inhab (coq_var v.var_name)) true) types in
  types @ inhab_h


let rec case (p, _, t) = coq_pattern p, coq_term t
and bool_case al p t =
  let t = coq_term t in
  let eq_true x = coq_app (Coq_var "Gospel.bool_to_prop") x in
  coq_pattern p, Coq_lettuple(al, coq_tuple (List.map eq_true al), t)

and to_prop_case t l =
  let bop = coq_var "Gospel.prop_to_bool" in
  let t = coq_app bop t in
  let branches =
    List.map (fun (p, g, t) ->
        let al = get_aliases p in
        if al = [] then case (p, g, t) else bool_case al p t) l in 
  coq_match t branches

and coq_term ?(poly_vars=[]) t =
    match t.Tterm.t_node with
    | Tvar v -> coq_id v.vs_name
    | Tconst c -> coq_const c
    | Tapp (_, f, [t]) when
           is_ignore (mk_qualid f.ls_name.id_str f.ls_name.id_path) ->
       (coq_term ~poly_vars) t
    | Tapp (_, f, [t1; t2])
         when f.ls_name.id_str = "apply" ->
       coq_app (coq_term ~poly_vars t1) (coq_term ~poly_vars t2)
    | Tapp (_, f, t1::t) when
           ls_equal f ps_equ &&
             ty_equal t1.t_ty ty_bool ->
       let ct1 = coq_term ~poly_vars t1 in
       let arg_maybe = List.map (coq_term ~poly_vars) t in 
       coq_apps (coq_var "Coq.Init.Logic.iff") (ct1::arg_maybe)
    | Tapp (_, f, []) when ls_equal f fs_bool_true  ->
       coq_prop_true
    | Tapp (_, f, []) when ls_equal f fs_bool_false  ->
       coq_prop_false
    | Tapp (qual, f, []) ->
       let poly = Tast2sep.get_poly t.t_ty in
       let var = coq_id f.ls_name in
       let var =
         match var with
         |Coq_var v ->
           let name = qual_var qual v in
           let name = if poly = [] then name else "@" ^ name in
           Coq_var name |_ -> assert false in
       let targs =
         List.concat_map
           (fun tv ->
             [Coq_var tv.tv_name.id_str;
              Coq_var (tv.tv_name.id_str^"Ih")]) poly in
       coq_apps var targs
    | Tapp (qual, f, args) ->
       let var = coq_id ~qual f.ls_name in
       coq_apps var (List.map (coq_term ~poly_vars) args)
    | Tfield _ -> assert false
    | Tif(g, th, el) ->
       let gc = coq_term ~poly_vars g in
       let thc = coq_term ~poly_vars th in
       let elc = coq_term ~poly_vars el in
       coq_if_prop gc thc elc
    | Tcase (t, l) ->
       let e = coq_term ~poly_vars t in 
       if ty_equal t.t_ty ty_bool then
         to_prop_case e l
       else
         coq_match e (List.map case l)
    | Tquant(q, ids, t) ->
       let f = match q with |Tforall -> coq_foralls |Texists -> coq_exists in
       let ids = List.map gen_args ids in
       let quant = f ids (coq_term ~poly_vars t) in       
       coq_foralls (gen_poly poly_vars) quant
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

let cfml_term poly_vars = function
  | Pure t -> hpure (coq_term ~poly_vars t)
  | App (sym, l) ->
      let loc = List.hd l in
      let rep = List.nth l (List.length l - 1) in
      hdata (coq_term loc)
        (coq_app (coq_id sym.ls_name) (coq_term rep))
  
let gen_spec triple =
  let poly_vars = triple.triple_poly in 
  let poly = gen_poly poly_vars in
  let encs = List.map (fun x -> enc_arg x.tv_name.id_str) poly_vars in
  
  let args = List.map gen_args_opt triple.triple_args in
  let all_vars = List.map gen_args triple.triple_vars in
  let dynargs = List.map (fun v -> coq_dyn_of v.var_type (coq_var v.var_name)) args in
  let trm = trm_apps_lifted (coq_var ("_"^triple.triple_name.id_str)) dynargs in
  let mk_condition tl =
    hstars (List.map (cfml_term poly_vars) tl) in
  let pre = mk_condition triple.triple_pre in
  let rets =
    match triple.triple_rets with
    | [] -> [ tv "_" coq_typ_unit false ]
    | rets ->
       let f v = tv v.vs_name.id_str (var_of_ty ~b2p:false v.vs_ty) false in
       List.map f rets in
  let mk_post (vl, tl) =
    let post = mk_condition tl in
    List.fold_right
      (fun v acc -> hexists v.vs_name.id_str (var_of_ty v.vs_ty) acc)
      vl post
  in
  let post = coq_funs rets (mk_post triple.triple_post) in
  let coq_triple = coq_apps_var "CFML.SepLifted.Triple" [ trm; pre; post ] in
  let check =
    coq_impls
      (List.map (fun x -> coq_term ~poly_vars x) triple.triple_checks)
      coq_triple in
  let triple_vars = coq_foralls all_vars check in
  coq_foralls (poly@encs) triple_vars

let mk_enc s = "_Enc_" ^ s

let rec sep_def d =
  match d.d_node with
  | Type tdef ->     
     let ty = coq_impls (List.map (fun _ -> Coq_type) tdef.type_args) Coq_type in
     let nm = tdef.type_name.id_str in
     let ty_decl = tv nm ty false in
     let self_ty =
       coq_apps (coq_var nm)
         (coq_vars (List.map (fun x-> x.tv_name.id_str) tdef.type_args)) in
     let poly =
       List.map
         (fun x -> tv x.tv_name.id_str Coq_type false) tdef.type_args in 
     let self_ty_vars =
       coq_foralls poly (enc_type self_ty) in
     let enc_name_par = "__Enc_" ^ nm in
     let enc_name = "_Enc_" ^ nm in
     let term = Coq_var enc_name_par in 
     [
      Coqtop_param ty_decl;
      Coqtop_param (tv enc_name_par self_ty_vars false);
      Coqtop_instance (tv enc_name self_ty_vars false, Some term, false);
     ]
  | Pred pred ->
     let args = List.rev pred.pred_args in
     let poly = gen_poly pred.pred_poly in
     let encs = List.map (fun x -> enc_arg x.tv_name.id_str) pred.pred_poly in
     let types = List.map (fun v -> var_of_ty v.vs_ty) args in
     let t = coq_impls types hprop in
     let with_poly = coq_foralls (poly@encs) t in
     [ Coqtop_param (tv (valid_coq_id pred.pred_name.id_str) with_poly false) ]
  | Triple triple ->
     let fun_def = tv ("_"^triple.triple_name.id_str) Formula.func_type false in
     let fun_triple = gen_spec triple in
     let triple_name = to_triple triple.triple_name.id_str in
     coqtop_params [ fun_def; tv triple_name fun_triple false ]
  | Function (poly, f) ->
     let name = valid_coq_id f.fun_ls.ls_name.id_str in
     let args = f.fun_params in
     let ret = f.fun_ls.ls_value in
     let ret_coq = var_of_ty ret in
     let args_coq =
       List.map (fun arg -> tv arg.vs_name.id_str (var_of_ty arg.vs_ty) false) args in
     let poly_types = gen_poly poly in
     let def = Option.map coq_term f.fun_def in
     begin match def with
     |Some d ->
       let coq_def = name, poly_types @ args_coq, ret_coq, d in
       if f.fun_rec then
         [coqtop_fixdef coq_def]
       else
         [coqtop_fundef coq_def]
     |None ->
       let t = coq_impls (List.map (fun x-> x.var_type) args_coq) ret_coq in
       let poly_args = coq_foralls poly_types t in
       coqtop_params [tv name poly_args false] end
  | Axiom (poly, a) ->
     let poly_types = gen_poly poly in 
     coqtop_params [tv a.ax_name.id_str (coq_foralls poly_types (coq_term a.ax_term)) false]
  | Module (nm, l) ->
     let statements = List.concat_map sep_def l in
     let nm_var = valid_coq_id nm.id_str in
     let m = Coqtop_module(nm_var, [], Mod_cast_free, Mod_def_declare) in
     m :: statements @ [Coqtop_end nm_var]
  | Import l -> [ Coqtop_import (List.map valid_coq_id l) ]
     
let sep_defs l =
  let cfml = List.map (fun s -> "CFML." ^ s) in
  let imports =
    [
      Coqtop_set_implicit_args;
      Coqtop_require_import [ "gospelstdlib_verified" ];
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
