(* Alex Schlumpf
   I pledge my honor that I have abied by the Stevens Honor System. *)
open Bindlib
open Ast

type 'a error = OK of 'a | Error of string

module Ctx = Map.Make(String)

let domain : texpr -> texpr error = fun t ->
  match t with 
    | FuncType (a, b) -> OK a
    | _ -> Error "Not a function"

let codomain : texpr -> texpr error = fun t ->
  match t with 
    | FuncType (a, b) -> OK b 
    | _ -> Error "Not a function"

let de_ok = fun e ->
  match e with 
    | OK x -> x
    | _ -> failwith "code should not reach this point"

let rec synthesize : texpr Ctx.t -> term -> texpr error = fun gamma m ->
  (match m with
    | CstTrue ->  OK BoolType
    | CstFalse -> OK BoolType
    | Var(x) -> (try OK (Ctx.find (name_of x) gamma)
                with Not_found -> Error "Type of variable could not be resolved")
    | App(t1, t2) -> 
      let type_of_t1 = synthesize gamma t1 
      in (match type_of_t1 with
        | OK FuncType _ -> 
          let type_of_t2 = check gamma t2 (de_ok (domain @@ de_ok type_of_t1)) in 
          (match type_of_t2 with
          | OK _ -> OK (de_ok (codomain @@ de_ok type_of_t1))
          | Error _ -> Error "Types of domain and parameter do not coincide.")
        | _ -> Error "Cannot apply non-function to parameter.")
    | TDecl(prog, t) -> 
      let type_of_prog = check gamma prog t
      in (match type_of_prog with 
          | OK r when (r = t) -> OK r
          | _ -> Error "Invalid type declaration.")
    | _ -> Error "Type error.")
and check : texpr Ctx.t -> term -> texpr -> texpr error = fun gamma m sigma ->
  match m with
    | Abs(f)-> 
      let (x, t) = unbind f in
      let type_of_t = check (Ctx.add (name_of x) (de_ok (domain sigma)) gamma) t (de_ok (codomain sigma)) in 
      (match type_of_t with 
      | t when (t = codomain sigma) -> OK sigma 
      | _ -> Error "Invalid abstraction")
    | ITE(cond, t1, t2) -> 
      (match check gamma cond BoolType with
        | OK BoolType -> 
          let type_of_t1 = check gamma t1 sigma in 
          let type_of_t2 = check gamma t2 sigma in 
          if (type_of_t1 = type_of_t2)
          then OK sigma 
          else Error "Types of if evaluations do not coincide."
        | _ -> Error "Type of condition must be bool.")
    | _ -> 
      let type_of_m = synthesize gamma m in 
      (match type_of_m with 
        | OK t -> if (de_ok type_of_m) = sigma 
                  then type_of_m 
                  else Error "Types do not coincide."
        | Error e -> Error e)

      

let tc : term -> texpr error = synthesize Ctx.empty
