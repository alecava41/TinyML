(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env0, x, e0) -> eval_expr ((x, v2) :: env0) e0
        | RecClosure (env0, f, x, e0) -> eval_expr ((x, v2) :: (f, v1) :: env0) e0
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    | LetRec (f, _, e1, e2) -> 
        let v1 = eval_expr env e1
        let vc = 
            match v1 with
            | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
            | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        
        eval_expr ((f,vc) :: env) e2

    | BinOp (e1, "+", e2) -> binop_arithmetic_int (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop_arithmetic_int (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop_arithmetic_int ( * ) env e1 e2
    | BinOp (e1, "/", e2) -> binop_arithmetic_int (/) env e1 e2
    | BinOp (e1, "%", e2) -> binop_arithmetic_int (%) env e1 e2

    | BinOp (e1, "+.", e2) -> binop_arithmetic_float (+) env e1 e2
    | BinOp (e1, "-.", e2) -> binop_arithmetic_float (-) env e1 e2
    | BinOp (e1, "*.", e2) -> binop_arithmetic_float ( * ) env e1 e2
    | BinOp (e1, "/.", e2) -> binop_arithmetic_float (/) env e1 e2

    | BinOp (e1, "<", e2) -> binop_comparison_int (<) env e1 e2
    | BinOp (e1, "<=", e2) -> binop_comparison_int (<=) env e1 e2
    | BinOp (e1, ">", e2) -> binop_comparison_int (>) env e1 e2
    | BinOp (e1, ">=", e2) -> binop_comparison_int (>=) env e1 e2
    | BinOp (e1, "=", e2) -> binop_comparison_int (=) env e1 e2
    | BinOp (e1, "<>", e2) -> binop_comparison_int (<>) env e1 e2

    | BinOp (e1, "<.", e2) -> binop_comparison_float (<) env e1 e2
    | BinOp (e1, "<=.", e2) -> binop_comparison_float (<=) env e1 e2
    | BinOp (e1, ">.", e2) -> binop_comparison_float (>) env e1 e2
    | BinOp (e1, ">=.", e2) -> binop_comparison_float (>=) env e1 e2
    | BinOp (e1, "=.", e2) -> binop_comparison_float (=) env e1 e2
    | BinOp (e1, "<>.", e2) -> binop_comparison_float (<>) env e1 e2

    | BinOp (e1, "and", e2) -> binop_comparison_bool (&&) env e1 e2
    | BinOp (e1, "or", e2) -> binop_comparison_bool (||)  env e1 e2

    | UnOp ("not", e) -> unop_not (not) env e
    | UnOp ("neg", e) -> unop_neg_int (~-) env e
    | UnOp ("neg.", e) -> unop_neg_float (~-) env e

    | Tuple es -> VTuple (List.map (eval_expr env) es)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and binop_arithmetic_int op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary int arithmetic operator: %s, %s" (pretty_value v1) (pretty_value v2)

and binop_arithmetic_float op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary float arithmetic operator: %s, %s" (pretty_value v1) (pretty_value v2)

and binop_comparison_int op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary int comparison operator: %s, %s" (pretty_value v1) (pretty_value v2)

and binop_comparison_float op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary float comparison operator: %s, %s" (pretty_value v1) (pretty_value v2)

and binop_comparison_bool op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LBool x), VLit (LBool y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary boolean comparison operator: %s, %s" (pretty_value v1) (pretty_value v2)

and unop_not op env e =
    let v = eval_expr env e
    match v with
    | VLit (LBool x) -> VLit (LBool (op x))
    | _ -> unexpected_error "eval_expr: illegal operands in unary not operator: %s" (pretty_value v)

and unop_neg_int op env e =
    let v = eval_expr env e
    match v with
    | VLit (LInt x) -> VLit (LInt (op x))
    | _ -> unexpected_error "eval_expr: illegal operands in unary int neg operator: %s" (pretty_value v)

and unop_neg_float op env e =
    let v = eval_expr env e
    match v with
    | VLit (LFloat x) -> VLit (LFloat (op x))
    | _ -> unexpected_error "eval_expr: illegal operands in unary float neg operator: %s" (pretty_value v)