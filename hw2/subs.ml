open Ast

type subst = (string,Ast.texpr) Hashtbl.t

let un_some x = match x with 
    | Some y -> y
    | _ -> failwith "expected Some x"

let create : subst = Hashtbl.create 16

let extend (subs : subst) name texpr = Hashtbl.add subs name texpr

let remove (subs : subst) name = Hashtbl.remove subs name

let lookup (subs : subst) name = Hashtbl.find_opt subs name

let rec apply_to_texpr (subs : subst) texpr = match (texpr) with
    | VarType name -> un_some (lookup subs name) 
    | FuncType (domain, codomain) -> FuncType (apply_to_texpr subs domain, apply_to_texpr subs codomain)
    | RefType r -> RefType (apply_to_texpr subs r)
    | t -> t

let rec apply_to_expr (subs : subst) expr  = match (expr) with
    | Letrec (tres, name, param, tparam, e, body) -> 
        Letrec (apply_to_texpr subs tres, name, param 
            , apply_to_texpr subs tparam, apply_to_expr subs e, apply_to_expr subs body)
    | Proc (param, tparam, body) -> Proc (param, apply_to_texpr subs tparam, apply_to_expr subs body)
    | e -> e

let s_func (subs : subst) name old_type = lookup subs name

let apply_to_env (subs : subst) (env : subst) = 
    Hashtbl.filter_map_inplace ((fun tbl -> fun name -> fun old_type -> lookup tbl name) subs) env

let domain (subs : subst) = Hashtbl.fold ((fun name -> fun _ -> fun names -> name::names)) subs []

(* let union 

let join (subs : subst list) = List.fold_left union create subs *)



