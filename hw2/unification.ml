open Ast


type  unif_result = UOk of Subs.subst | UError of texpr*texpr

let not_vartype t = match t with 
    | VarType v -> false
    | _ -> true

let rec in_free_var f name = match f with 
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
                (* 4. Variable Elimination *)
                | VarType name, t2 when not (in_free_var (VarType name) t2) ->
                    Subs.extend subs name t2;
                    mgu_helper t subs
                (* 6. Occur Check *)
                (* | t1, t2 when  *)
                | _ -> failwith ""

let mgu (g : (Ast.texpr*Ast.texpr) list) : unif_result = mgu_helper g (Subs.create ())

