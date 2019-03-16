open Unification
open Subs
open Ast


type 'a error = OK of 'a | Error of string

type typing_judgement = subst*expr*texpr

let fresh_name (n:int) : string = "_V" ^ (string_of_int n)

let un_tag (tj : 'a error) = match tj with 
  | OK tj -> tj 
  | Error _ -> failwith "expected an OK" 

let un_some s = match s with 
  | Some x -> x 
  | None -> failwith "Expected a Some"

let find_common_name (b_name:string) (b_type:Ast.texpr) (tup:subst*((texpr*texpr) list) ) : subst*((texpr*texpr) list) = 
  let (g2, accum) = tup in
  match lookup g2 b_name with 
    | Some t -> (g2, (t, b_type) :: accum)
    | None -> (g2, accum)

let compat g1 g2 = let (_, res) = Hashtbl.fold find_common_name g1 (g2, []) in res


let rec infer' (e:expr) (n:int): (int*typing_judgement) error =
  match e with
  | Unit ->  let tbl = create () in OK (n, (tbl,e,UnitType))
  | Var s -> 
    let tbl = create() in 
    let t = VarType (fresh_name n) in 
    extend tbl s t;
    OK (n+1, (tbl, e, t))
  | Int num -> let tbl = create () in OK (n, (tbl,e,IntType))
  | Add(e1, e2)  -> 
    let e1_inf = infer' e1 n in 
    (match e1_inf with 
    | OK (w,(gamma1, exp1, texp1)) -> 
      let e2_inf = infer' e2 (w) in 
      (match e2_inf with 
        | OK (z,(gamma2, exp2, texp2)) -> 
          let unify = mgu ([(texp1, IntType); (texp2, IntType)] @ (compat gamma1 gamma2)) in 
          (match unify with 
            | UOk subs -> 
              apply_to_env subs gamma1;
              apply_to_env subs gamma2; 
              let sexp = Add(apply_to_expr subs exp1, apply_to_expr subs exp2) in 
              let union = join ([gamma1; gamma2]) in
              OK ((z), (union, sexp, IntType))
            | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
        | Error x -> Error x)
    | Error x -> Error x)
  | Sub(e1, e2)  -> 
    let e1_inf = infer' e1 n in 
    (match e1_inf with 
    | OK (w,(gamma1, exp1, texp1)) -> 
      let e2_inf = infer' e2 (w) in 
      (match e2_inf with 
        | OK (z,(gamma2, exp2, texp2)) -> 
          let unify = mgu ([(texp1, IntType); (texp2, IntType)] @ (compat gamma1 gamma2)) in 
          (match unify with 
            | UOk subs -> 
              apply_to_env subs gamma1;
              apply_to_env subs gamma2; 
              let sexp = Sub(apply_to_expr subs exp1, apply_to_expr subs exp2) in 
              let union = join ([gamma1; gamma2]) in
              OK ((z), (union, sexp, IntType))
            | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
        | Error x -> Error x)
    | Error x -> Error x)
  | Div(e1, e2)  -> 
    let e1_inf = infer' e1 n in 
    (match e1_inf with 
    | OK (w,(gamma1, exp1, texp1)) -> 
      let e2_inf = infer' e2 (w) in 
      (match e2_inf with 
        | OK (z,(gamma2, exp2, texp2)) -> 
          let unify = mgu ([(texp1, IntType); (texp2, IntType)] @ (compat gamma1 gamma2)) in 
          (match unify with 
            | UOk subs -> 
              apply_to_env subs gamma1;
              apply_to_env subs gamma2; 
              let sexp = Div(apply_to_expr subs exp1, apply_to_expr subs exp2) in 
              let union = join ([gamma1; gamma2]) in
              OK ((z), (union, sexp, IntType))
            | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
        | Error x -> Error x)
    | Error x -> Error x)
  | Mul(e1, e2)  -> 
    let e1_inf = infer' e1 n in 
    (match e1_inf with 
    | OK (w,(gamma1, exp1, texp1)) -> 
      let e2_inf = infer' e2 (w) in 
      (match e2_inf with 
        | OK (z,(gamma2, exp2, texp2)) -> 
          let unify = mgu ([(texp1, IntType); (texp2, IntType)] @ (compat gamma1 gamma2)) in 
          (match unify with 
            | UOk subs -> 
              apply_to_env subs gamma1;
              apply_to_env subs gamma2; 
              let sexp = Mul(apply_to_expr subs exp1, apply_to_expr subs exp2) in 
              let union = join ([gamma1; gamma2]) in
              OK ((z), (union, sexp, IntType))
            | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
        | Error x -> Error x)
    | Error x -> Error x)
  | NewRef(e1) -> 
    let e1_inf = infer' e1 n in
      (match e1_inf with 
        | OK (m, (gamma, expr, texp)) -> OK (m, (gamma, apply_to_expr gamma e, RefType (texp)))
        | Error x -> Error x)
  | DeRef(e1) -> (match infer' e1 n with 
    | OK (m, (gamma, expr, texpr)) -> let name = fresh_name m in 
      (match (mgu [texpr, RefType(VarType(name))]) with
        | UOk subs -> 
          apply_to_env subs gamma;
          OK (m+1, (gamma, DeRef(apply_to_expr subs expr), apply_to_texpr subs (VarType name)))
        | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
    | Error x -> Error x)
  | SetRef(e1, e2) -> 
    (match (infer' e1 n) with 
      | OK (m, (r_gamma, r_expr, r_type)) -> 
        (match (infer' e2 m) with 
          | OK (z, (b_gamma, b_expr, b_type)) -> 
            (match (mgu [r_type, RefType(b_type)]) with 
              | UOk subs1 -> 
                apply_to_env subs1 r_gamma;
                apply_to_env subs1 b_gamma;
                (match mgu (compat r_gamma b_gamma) with 
                  | UOk subs2 -> 
                    let subs = join [subs1; subs2] in 
                    apply_to_env subs r_gamma;
                    apply_to_env subs b_gamma;
                    let gamma = join [r_gamma; b_gamma] in
                    let sexp = SetRef(apply_to_expr subs r_expr, apply_to_expr subs b_expr) in
                    OK(z, (gamma, sexp, UnitType))
                  | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
              | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
          | Error x -> Error x)
      | Error x -> Error x)
  | Let(x,def,body) -> 
    let def_inf = infer' def n in 
    (match def_inf with
      | OK (m, (d_gamma, d_exp, d_texp)) -> 
        let body_inf = infer' body (m+1) in 
        (match body_inf with 
          | OK (z, (b_gamma, b_exp, b_texp)) ->
            (* print_string ((string_of_subs b_gamma) ^ "\n"); *)
            let t_def_in_body = lookup b_gamma x in 
            (match t_def_in_body with 
              | Some t_d -> let unify = mgu ([d_texp, t_d]) in 
                (match unify with
                  | UOk subs1 -> 
                    apply_to_env subs1 d_gamma;
                    apply_to_env subs1 b_gamma;
                    (match (mgu (compat b_gamma d_gamma)) with 
                      | UOk subs2 ->
                        let subs  = join [subs1; subs2] in   
                        apply_to_env subs d_gamma;
                        apply_to_env subs b_gamma;                  
                        let sdef = apply_to_expr subs d_exp in 
                        let sbody = apply_to_expr subs b_exp in 
                        let stexp = apply_to_texpr subs b_texp in 
                        OK ((z), (join [b_gamma; d_gamma], Let(x, sdef, sbody), stexp))
                      | UError(x,y) ->  Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))

                  | UError (x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
              | None -> OK ((z+1), (create (), Let(x, d_exp, b_exp), b_texp)))

          | Error x -> Error x)
      | Error x -> Error x)
  | Proc(x,t,body) -> (match infer' body n with 
    | OK (m, (gamma, exp, tb)) -> OK (n, (create (), Proc(x,t,body), FuncType(t,tb)))
    | Error x -> Error x)
  | ProcUntyped(x,body) -> (match (infer' body n) with 
    | OK (m, (b_gamma, b_expr, b_type)) -> 
      (match lookup b_gamma x with
        | Some t -> 
          remove b_gamma x; 
          OK (m, (b_gamma, Proc(x, t, b_expr), FuncType(t, b_type)))
        | None -> let name = fresh_name m in 
          OK (m+1, (b_gamma, Proc(x, VarType name, b_expr), FuncType(VarType name, b_type))))
    | Error x -> Error x)
  | App(e1, e2) -> (match (infer' e1 n) with 
    | OK (m, (f_gamma, f_expr, f_type)) -> 
      (match (infer' e2 m) with 
        | OK (z, (p_gamma, p_expr, p_type)) -> 
          let new_name = fresh_name z in 
          (match (mgu [f_type, FuncType(p_type, (VarType new_name))]) with 
            | UOk subs1 ->
              apply_to_env subs1 f_gamma;
              apply_to_env subs1 p_gamma;
              (match mgu (compat f_gamma p_gamma) with 
                | UOk subs2 -> 
                  let subs = join [subs1; subs2] in
                  apply_to_env subs f_gamma;
                  apply_to_env subs p_gamma;
                  let gamma = join [f_gamma; p_gamma] in 
                  OK ((z+1), (gamma, App(apply_to_expr subs f_expr, apply_to_expr subs p_expr), apply_to_texpr subs (VarType new_name)))
                | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
            | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
        | Error x -> Error x)
    | Error x -> Error x)
  | IsZero(exp) -> (match (infer' exp n) with 
    | OK (m, (exp_gamma, expr, texp)) -> 
      let unify = mgu ([texp, IntType]) in 
      (match unify with 
        | UOk subs -> 
          apply_to_env subs exp_gamma;
          OK (m, (exp_gamma, (apply_to_expr subs (IsZero(expr))), BoolType)) 
        | UError (x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
    | Error x -> Error x)
  | ITE(e1,e2,e3) -> (match (infer' e1 n) with 
    | OK (m, (c_gamma, c_exp, c_type)) -> let c_unify = mgu ([c_type, BoolType]) in 
      (match c_unify with
        | UOk c_subs -> 
          (match infer' e2 m with 
            | OK (z, (b1_gamma, b1_exp, b1_type)) -> 
              (match infer' e3 z with 
                | OK (w, (b2_gamma, b2_exp, b2_type)) -> 
                  let unify = mgu ([(b1_type, b2_type)]) in 
                  (match unify with 
                    | UOk subs1 -> 
                      apply_to_env subs1 c_gamma;
                      apply_to_env subs1 b1_gamma;
                      apply_to_env subs1 b2_gamma;
                      let compat_res = (compat c_gamma b1_gamma) @ (compat c_gamma b2_gamma) @ (compat b1_gamma b2_gamma) in 
                      (match (mgu compat_res) with 
                        | UOk subs2 ->
                          let subs = join [subs1; subs2] in                    
                          apply_to_env subs c_gamma;
                          apply_to_env subs b1_gamma;
                          apply_to_env subs b2_gamma;
                          let env = join [c_gamma; b1_gamma; b2_gamma] in 
                          let sexp = ITE(apply_to_expr subs c_exp, apply_to_expr subs b1_exp, apply_to_expr subs b2_exp) in 
                          let stexp = apply_to_texpr subs b1_type in
                          OK (w+1, (env, sexp, stexp)) 
                        | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))

                    | UError (x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
                | Error x -> Error x)
            | Error x -> Error x)
        | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
    | Error x -> Error x)
  | Letrec(tRes, x, param, tPara, def, body) -> failwith "not implemented!"
  (* Four cases:
    1. f is defined and run in the body.
      -f's type in the def and the body must be unifiable
    2. f is defined and not run in the body 
      -f's type is the type inferred in the def
    3. f is not defined and run in the body 
      -f's type is the type inferred in the body
      -param's type is the domain of f if f is a function, and fresh otherwise
    4. f is neither defined nor run in the body
      -f takes on a fresh type, so does param
    Common: 
      -f must be unifiable with the arrow type
      -the environments of the def and body must be compatible *)
  | LetrecUntyped(f, param, def, body) -> (match infer' def n with 
    | OK (m, (d_gamma, d_expr, d_type)) -> (match infer' body m with
      | OK(z, (b_gamma, b_expr, b_type)) ->
        (match lookup d_gamma f with 
          | Some fd_type ->
            (match (lookup b_gamma f) with 
              (* Case 1 *)
              | Some fb_type -> 
                let domain = fresh_name z in 
                let codomain = fresh_name (z+1) in 
                (match mgu ([(fd_type, fb_type); (fd_type, FuncType(VarType domain, VarType codomain))]) with 
                  | UOk subs1 ->
                    apply_to_env subs1 d_gamma;
                    apply_to_env subs1 b_gamma;
                    (match mgu (compat b_gamma d_gamma) with 
                      | UOk subs2 -> 
                        let subs = join [subs1; subs2] in 
                        apply_to_env subs b_gamma;
                        apply_to_env subs d_gamma;
                        let gamma = join [b_gamma; d_gamma] in 
                        let dom = apply_to_texpr subs (VarType domain) in 
                        let cod = apply_to_texpr subs (VarType codomain) in
                        let sdef = apply_to_expr subs d_expr in 
                        let sbody = apply_to_expr subs b_expr in
                        let stype = apply_to_texpr subs b_type in 
                        OK ((z+2), (gamma, Letrec(dom, f, param, cod, sdef, sbody), stype))
                      | UError(x,y) ->  Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
                  | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y)))
              (* Case 2 *)
              | None -> 
                let domain = fresh_name z in 
                let codomain = fresh_name (z+1) in 
                (match (mgu [fd_type, (FuncType(VarType domain, VarType codomain))]) with 
                  | UOk subs1 -> 
                    apply_to_env subs1 d_gamma;
                    apply_to_env subs1 b_gamma;
                    (match mgu (compat b_gamma d_gamma) with 
                      | UOk subs2 ->
                        let subs = join [subs1; subs2] in 
                        apply_to_env subs b_gamma;
                        apply_to_env subs d_gamma;
                        let gamma = join [b_gamma; d_gamma] in 
                        let dom = apply_to_texpr subs (VarType domain) in 
                        let cod = apply_to_texpr subs (VarType codomain) in
                        let sdef = apply_to_expr subs d_expr in 
                        let sbody = apply_to_expr subs b_expr in
                        let stype = apply_to_texpr subs b_type in 
                        OK ((z+2), (gamma, Letrec(dom, f, param, cod, sdef, sbody), stype))
                      | UError(x,y) -> failwith "")
                  | UError(x,y) -> Error ("Cannot unify " ^ (string_of_texpr x) ^ " and " ^ (string_of_texpr y))))
          | None -> 
            (match lookup b_gamma f with 
              (* Case 3 *)
              | Some fb_type -> failwith "case 3"
              (* Case 4 *)
              | None -> failwith "case 4"))
      | Error x -> Error x)
    | Error x -> Error x) 
  | BeginEnd(es) -> failwith ""


let string_of_typing_judgement tj = let (subs, e, t) = tj in
  (string_of_subs subs)^"|- "^(string_of_expr e)^": "^ (string_of_texpr t)


let infer_type (AProg e) =
  match infer' e 0 with
  | OK (_, tj) -> string_of_typing_judgement tj
  | Error s -> "Error! "^ s



let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

(* Interpret an expression *)
let inf (e:string) : string =
  e |> parse |> infer_type 

let test (n:int) : string =
  Examples.expr n |> parse |> infer_type 
