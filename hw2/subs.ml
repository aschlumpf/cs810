open Ast

type subst = (string,Ast.texpr) Hashtbl.t

let un_some x = match x with 
    | Some y -> y
    | _ -> failwith "expected Some x"

let create () : subst = Hashtbl.create 16

let extend (subs : subst) name texpr = Hashtbl.add subs name texpr

let remove (subs : subst) name = Hashtbl.remove subs name

let lookup (subs : subst) name = Hashtbl.find_opt subs name

let rec apply_to_texpr (subs : subst) texpr = match (texpr) with
    | VarType name -> (match (lookup subs name) with
        | Some x -> x 
        | None -> VarType name)
    | FuncType (domain, codomain) -> FuncType (apply_to_texpr subs domain, apply_to_texpr subs codomain)
    | RefType r -> RefType (apply_to_texpr subs r)
    | t -> t

let rec apply_to_expr (subs : subst) expr  = match (expr) with
    | Letrec (tres, name, param, tparam, e, body) -> 
        Letrec (apply_to_texpr subs tres, name, param 
            , apply_to_texpr subs tparam, apply_to_expr subs e, apply_to_expr subs body)
    | ProcUntyped (param, body) -> ProcUntyped(param, apply_to_expr subs body)
    | Proc (x, tparam, body) -> Proc(x, apply_to_texpr subs tparam, apply_to_expr subs body)
    | e -> e

let s_func (subs : subst) name old_type = lookup subs name

let replace (subs : subst) (binding_name : string) (binding_type : Ast.texpr) : Ast.texpr option = 
    match binding_type with 
        | VarType name as t -> Some(apply_to_texpr subs t)
        | RefType(VarType name) as t-> Some(apply_to_texpr subs t)
        | FuncType(x,y) as t-> Some(apply_to_texpr subs t)    
        | x -> Some x

let apply_to_env (subs : subst) (env : subst) : unit = 
    Hashtbl.filter_map_inplace (replace subs) env
    (* Hashtbl.filter_map_inplace ((fun tbl -> fun name -> fun old_type -> lookup tbl name) subs) env *)

let domain (subs : subst) =
    Hashtbl.fold ((fun name -> fun _ -> fun names -> name::names)) subs []

let string_of_binding name typ buff = 
    Buffer.add_string buff (name^" := "^ string_of_texpr typ ^ ", "); buff

let string_of_subs (subs : subst) : string = 
    if ((Hashtbl.length subs) == 0)
    then "empty "
    else let buff = Buffer.create 16 in
    Buffer.add_string (Hashtbl.fold string_of_binding subs buff) "";
    Buffer.contents buff


let build_table (accum : subst) (subs : subst) = 
    Hashtbl.iter (Hashtbl.replace accum) subs; accum 

let join (subs_list : subst list) : subst = 
    let accum = create () in
    List.fold_left build_table accum subs_list



