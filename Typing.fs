(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list

(*
    -------------
    UTILITY STUFF
    -------------
*)

let type_error fmt = throw_formatted TypeError fmt

let mutable tyVarCounter = 0

// fresh_tyvar is a utility function to get a fresh type variable
let fresh_tyvar (): ty = 
    tyVarCounter <- tyVarCounter + 1
    TyVar tyVarCounter

// freevers_ty calculates the free type variables occurring on a type
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

// freevers_scheme calculates the free type variables occurring on a type scheme
let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

//freevers_scheme_env calculates the free type variables occurring on an environment
let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// apply_subst_ty applies a substitution to a type
let rec apply_subst_ty (t : ty) (s : subst) : ty =
    match t with 
    | TyName _ -> t
    | TyVar tv ->
        let po = List.tryFind (fun (t, _) -> t = tv) s

        match po with 
        | None -> t
        | Some (_, t) ->
            // avoid circularity
            let tvs = freevars_ty t

            if Set.contains tv tvs then type_error "Cannot apply substitution [%O -> %O], circularity not allowed" tv t
            else t

    | TyArrow (t1, t2) -> TyArrow (apply_subst_ty t1 s, apply_subst_ty t2 s)
    | TyTuple ts -> TyTuple (List.map (fun t -> apply_subst_ty t s) ts)

// apply_subst_scheme applies a substitution to a type scheme
let apply_subst_scheme (Forall (tvs, t)) (s: subst): scheme =
    let refined_subst = List.filter (fun (tv, _) -> not (Set.contains tv tvs)) s
    Forall (tvs, apply_subst_ty t refined_subst)
    
// apply_subst_scheme_env applies a substitution to an environment
let apply_subst_scheme_env (env: scheme env) (s: subst): scheme env =
    List.map (fun (id, sch) -> id, apply_subst_scheme sch s) env

// compose_subst composes a newer substitution with an older substitution
let compose_subst (s2 : subst) (s1 : subst) : subst = 
    let mapF (tv2, t2) =
        // looking for a substitution with the same domain in s1
        let po = List.tryFind (fun (tv, _) -> tv = tv2) s1

        match po with 
        | None -> tv2, t2
        | Some (_, t1) ->
            // handling domain "not disjoint" case
            if t1 <> t2 then type_error "Cannot compose substs with <> mappings for the same TyVar (s2 has [%d -> %O] while s1 has [%d -> %O])" tv2 t2 tv2 t1
            else  tv2, apply_subst_ty t2 s1

    (List.map mapF s2) @ s1

// utility operator for composing substitutions as defined in the litetature (s2 @@ s1)
let (@@) = compose_subst

// unify takes two types and calculates a substitution that makes the two types to be the same (Martelli - Montanari algorithm)
let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName s1, TyName s2 -> if s1 = s2 then [] else type_error "Cannot unify type constructors %s and %s" s1 s2
    
    | TyVar v, t
    | t, TyVar v -> List.singleton (v, t)

    | TyArrow (t1, t2), TyArrow (t3, t4) -> (unify t1 t3) @@ (unify t2 t4)

    | TyTuple ts1, TyTuple ts2 ->
        if List.length ts1 <> List.length ts2 then type_error "Cannot unify tuples of <> length"
        else List.fold (fun acc (t1, t2) -> (unify t1 t2) @@ acc) List.Empty (List.zip ts1 ts2)

    | _ -> type_error "Cannot unify types %O, %O" t1 t2

// generalize_scheme_env promotes a type to a type scheme by calculating which type variables are polymorphic
let generalize_scheme_env (t: ty) (env: scheme env) : scheme =
    let tvs = freevars_ty t - freevars_scheme_env env
    Forall (tvs, t)

// instantiate converts a type scheme to a type by refreshing its polymorphic type variables
let instantiate (Forall (tvs, t)) : ty = 
    let subst = Set.fold (fun acc tv -> (tv, fresh_tyvar ()) :: acc) List.Empty tvs
    apply_subst_ty t subst

// pretty_ty_tvs is a utility function (like Ast.pretty_tv), printing "greek" letters instead of numbers when dealing with type variables
let rec pretty_ty_tvs mappings t =
    match t with
    | TyName s -> s
    | TyArrow (TyArrow _ as t1, t3) -> sprintf "(%s) -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t3)
    | TyArrow (t1, t2) -> sprintf "%s -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t2)
    | TyVar n -> 
        let _, pretty_tv = List.find (fun (ftv, _) -> ftv = n) mappings
        sprintf "'%c" pretty_tv
    | TyTuple ts -> sprintf "(%s)" (pretty_tupled (pretty_ty_tvs mappings) ts)

// pretty_ty_v2 is a utility function for pretty printing types, also caring about type variables
let pretty_ty_v2 t =
    // safe to do it, type is always refined at its maximum when calling this function
    let ftvs = freevars_ty t

    if Set.count ftvs > 0 
        then
            // taking a list of "greek" letters to match the number of polymorphic type variables occuring on the type 
            let alphabet = List.truncate (Set.count ftvs) ['a' .. 'z']
            pretty_ty_tvs (List.zip (Set.toList ftvs) alphabet) t
        else Ast.pretty_ty t

(*
    --------------------------------------
    BASIC ENVIRONMENT (built-in operators)
    --------------------------------------
*)

// basic environment for type checking
let init_ty_env = [
    // binary int operators
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("%", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    (">", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    (">=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<>", TyArrow (TyInt, TyArrow(TyInt, TyBool)))

    // binary float operators
    ("+.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("*.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("/.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("<.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<>.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))

    // binary bool operators
    ("and", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ("or", TyArrow (TyBool, TyArrow(TyBool, TyBool)))

    // unary operators
    ("not", TyArrow (TyBool, TyBool))
    ("neg", TyArrow (TyInt, TyInt))
    ("neg.", TyArrow (TyFloat, TyFloat))
]

// basic environment for type inference
let init_scheme_env = List.map (fun (s, t) -> (s, Forall (Set.empty, t))) init_ty_env

(*
    ------------------------
    TYPE INFERENCE ALGORITHM
    ------------------------
*)
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, List.Empty 
    | Lit (LBool _) -> TyBool, List.Empty
    | Lit (LFloat _) -> TyFloat, List.Empty
    | Lit (LString _) -> TyString, List.Empty
    | Lit (LChar _) -> TyChar, List.Empty
    | Lit LUnit -> TyUnit, List.Empty

    | Var x ->         
        let po = List.tryFind (fun (y, _) -> x = y) env

        match po with
        | None -> type_error "Identifier %s not defined" x
        | Some (_, sch) -> instantiate sch, List.Empty

    | Lambda (x, tyo, e) ->
        let tv = fresh_tyvar ()
        let sch = Forall (Set.empty, tv)

        let t2, s = typeinfer_expr ((x, sch) :: env) e
        let t1 = apply_subst_ty tv s
        
        // handling optional explicit type annotation
        let s1 =
            match tyo with
            | None -> List.Empty
            | Some t -> unify t1 t

        TyArrow (apply_subst_ty t1 s1, t2), s1 @@ s

    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_subst_scheme_env env s1) e2

        let fresh_ty = fresh_tyvar ()

        let s3 = s2 @@ s1

        let s4 = unify (TyArrow (apply_subst_ty t2 s3, fresh_ty)) (apply_subst_ty t1 s3)
        
        apply_subst_ty fresh_ty s4, s4 @@ s3

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool

        let s3 = s2 @@ s1
        let t2, s4 = typeinfer_expr (apply_subst_scheme_env env s3) e2

        let s5 = s4 @@ s3

        // handling optional 'else' branch
        match e3o with
        | None ->
            let s6 = unify t2 TyUnit
            t2, s6 @@ s5
        | Some e3 ->
            let t3, s6 = typeinfer_expr (apply_subst_scheme_env env s5) e3
            
            let s7 = s6 @@ s5

            let s8 = unify (apply_subst_ty t2 s7) (apply_subst_ty t3 s7)
            apply_subst_ty t2 s8, s8 @@ s7

    | Tuple es ->
        let f (ts, s) exp = 
            let ti, si = typeinfer_expr (apply_subst_scheme_env env s) exp
            ts @ List.singleton (apply_subst_ty ti si), si @@ s

        let ts, s = List.fold f (List.Empty, List.Empty) es

        TyTuple ts, s

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1

        // handling optional explicit type annotation
        let s3 = 
            match tyo with
            | None -> List.empty
            | Some t -> unify t1 t

        let s4 = s3 @@ s1

        let sch = generalize_scheme_env (apply_subst_ty t1 s4) env

        let t2, s2 = typeinfer_expr ((x, sch) :: apply_subst_scheme_env env s4) e2

        let s5 = s2 @@ s4

        apply_subst_ty t2 s5, s5

    | LetRec (f, tfo, e1, e2) ->
        let f_sch = Forall (Set.empty, fresh_tyvar ())
        let t1, s1 = typeinfer_expr ((f, f_sch) :: env) e1

        let sch = generalize_scheme_env (apply_subst_ty t1 s1) env

        // handling optional explicit type annotation
        let s2 = 
            match tfo with
            | None -> List.empty
            | Some t -> unify t1 t

        let s3 = s2 @@ s1

        let t, s4 = typeinfer_expr ((f, sch) :: apply_subst_scheme_env env s3) e2

        let s5 = s4 @@ s3

        apply_subst_ty t s5, s5

    | BinOp (e1, op, e2) -> 
        if List.contains op (List.map (fun (s, _) -> s) init_scheme_env)
            then  
                // "transform" the expression in a function application ('a -> 'a -> 'b)
                typeinfer_expr env (App (App (Var op, e1), e2))
            else 
                unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp (op, e) ->
        if List.contains op (List.map (fun (s, _) -> s) init_scheme_env)
            then  
                // "transform" the expression in a function application ('a -> 'a)
                typeinfer_expr env (App (Var op, e))
            else 
                unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e


(*
    ------------------------
    TYPE CHECKING ALGORITHM
    ------------------------
*)
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, _, _) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
    
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1,  op, e2) ->
        if List.contains op (List.map (fun (s, _) -> s) init_ty_env)
            then  
                // "transform" the expression in a function application ('a -> 'a -> 'b)
                typecheck_expr env (App (App (Var op, e1), e2))
            else 
                unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp (op, e) ->
        if List.contains op (List.map (fun (s, _) -> s) init_ty_env)
            then  
                // "transform" the expression in a function application ('a -> 'a)
                typecheck_expr env (App (Var op, e))
            else 
                unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e