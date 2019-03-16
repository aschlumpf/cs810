open Ast


type  unif_result = UOk of Subs.subst | UError of texpr*texpr

let not_vartype t = match t with 
    | VarType v -> false
    | _ -> true

let not_unif t = match t with 
    | FuncType _ -> false 
    | VarType _ -> false
    | _ -> true

let rec in_free_var name f = match f with 
    | FuncType(a, b) when name = a || name = b -> true
    | FuncType(t1, t2) -> (in_free_var t1 name) || (in_free_var t2 name)
    | _ -> false 

let rec mgu_helper (g : (Ast.texpr*Ast.texpr) list) (subs : Subs.subst) : unif_result =
    match g with 
        | [] -> UOk subs
        | h::t ->
            let (t1, t2) = h in 
            match (t1,t2) with
                (* 1. Decomposition *)
                | FuncType(dom1,cod1), FuncType(dom2,cod2) -> 
                    mgu_helper ([dom1, dom2] @ [cod1, cod2] @ t) subs
                (* 2. Trivial Pair Elimination *)
                | (t1, t2) when t1 = t2 -> mgu_helper t subs
                (* 3. Swap *)
                | t1, VarType name when not_vartype t1 -> 
                    mgu_helper ([VarType name, t1] @ t) subs
                | VarType(name1), VarType(name2) when name1 < name2 -> 
                    mgu_helper ([VarType name2, VarType name1] @ t) subs
                (* 4. Variable Elimination *)
                | VarType name, t2 when not (in_free_var (VarType name) t2) ->
                    Subs.extend subs name t2;
                    mgu_helper t subs
                | RefType(t1), RefType(t2) -> mgu_helper ([t1,t2] @ t) subs
                (* 5. Fail *)
                | FuncType(x,y), t2 when not_unif t2 -> UError(FuncType(x,y), t2)
                | t1, FuncType(x,y) when not_unif t1 -> UError(t1, FuncType(x,y))
                | t1, t2 when t1 != t2 -> UError(t1, t2)
                (* 6. Occur Check *)
                | VarType name, t2 when in_free_var (VarType name) t2-> 
                    UError (VarType name, t2)
                | _ -> failwith "invalid input"

let replace subs (b_name:string) (b_type:Ast.texpr) : Ast.texpr option = 
    match b_type with 
        | VarType n -> 
            (match (Subs.lookup subs n) with 
                | Some x -> Some x
                | None -> Some b_type)
        | x -> Some x

let reduce tj = match tj with 
    | UOk subs -> Hashtbl.filter_map_inplace (replace subs) subs; UOk(subs)
    | UError (x,y) -> UError (x,y)

let mgu (g : (Ast.texpr*Ast.texpr) list) : unif_result = reduce (mgu_helper g (Subs.create ()))

let uf e = match (mgu e) with 
    | UOk subs -> Subs.string_of_subs subs
    | UError (x,y) -> "Error: ("^ string_of_texpr x ^", " ^ string_of_texpr y ^")";;