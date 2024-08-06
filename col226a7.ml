(* defining a custom exception for our krivine machine *)
exception KrivineMachineError of string;;

(* defining an algebraic datatype for lambda calculus expressions *)
type expr =
  | Var of string   (* variable *)
  | Abs of string * expr    (* lambda abstraction *)
  | App of expr * expr    (* function application *)
  | Num of int    (* integer *)
  | Plus of expr * expr   (* addition *)
  | Minus of expr * expr    (* subtraction *)
  | Times of expr * expr    (* multiplication *)
  | Divide of expr * expr   (* division *)
  | Mod of expr * expr    (* modulo *)
  | T   (* true *)
  | F   (* false *)
  | Equal of expr * expr    (* equality *)
  | Gt of expr * expr   (* greater than *)
  | Lt of expr * expr   (* less than *)
  | Gte of expr * expr    (* greater than or equal to *)
  | Lte of expr * expr    (* less than or equal to *)
  | Neq of expr * expr    (* not equal to *)
  | And of expr * expr    (* logical and *)
  | Or of expr * expr    (* logical or *)
  | Not of expr    (* logical not *)
  | Ifthenelse of expr * expr * expr    (* if then else *)

(* closure type-definition represtnting lambda function eith its environment *)
and closure = Closure of expr * environment
(* environment type-definition representing a list of string(variable)-closure pairs *)
and environment = (string * closure) list
(* stack type-definition representing a list of closures *)
type stack = closure list
(* defining a type for the configuration of the krivine machine *)
type config = closure * stack

(* Closures evaluation in the krivine machine.
  It takes a configuration `config` consisting of a closure and a stack,
  and returns a closure representing the result of the evaluation. *)
let rec krivine (config: config) : closure =
  match config with
  (* Pattern matching for the case when the closure is a conditional expression. *)
  | (Closure(Ifthenelse(cond, e_then, e_else), env), stack) ->
    (* We evaluate the conditional expression and match it to a number. *)
    let Closure(Num n, _) = krivine (Closure(cond, env), stack) in
    (* If the condition is true, we evaluate the then expression. *)
    if n != 0 then krivine (Closure(e_then, env), stack)  (* True condition *)
    (* If the condition is false, we evaluate the else expression. *)
    else krivine (Closure(e_else, env), stack)  (* False condition *)
  (* Pattern matching for the case when the closure is a boolean operation. *)
  | (Closure(And(e1, e2), env), stack) ->
    (* We evaluate the two expressions and perform the logical AND operation. *)
    let Closure(Num n1, _) = krivine (Closure(e1, env), []) in
    (* If the first expression evaluates to false, we return false. *)
    let Closure(Num n2, _) = krivine (Closure(e2, env), []) in
    (* If the second expression evaluates to false, we return false. *)
    Closure(Num (if n1 != 0 && n2 != 0 then 1 else 0), env)
    (* If both expressions evaluate to true, we return true. *)
| (Closure(Or(e1, e2), env), stack) ->
    (* We evaluate the two expressions and perform the logical OR operation. *)
    let Closure(Num n1, _) = krivine (Closure(e1, env), []) in
    (* If the first expression evaluates to true, we return true. *)
    let Closure(Num n2, _) = krivine (Closure(e2, env), []) in
    (* If the second expression evaluates to true, we return true. *)
    Closure(Num (if n1 != 0 || n2 != 0 then 1 else 0), env)
    (* If either of the expressions evaluates to true, we return true. *)
| (Closure(Not(e), env), stack) ->
    (* We evaluate the expression and perform the logical NOT operation. *)
    let Closure(Num n, _) = krivine (Closure(e, env), []) in
    (* If the expression evaluates to false, we return true. *)
    Closure(Num (if n == 0 then 1 else 0), env)
    (* If the expression evaluates to true, we return false. *)
  (* If the closure is a variable, we try to find its binding in the environment *)
  | (Closure(Var x, env), stack) ->
      (match List.assoc_opt x env with
      (* If the variable is bound, we return the closure associated with it *)
        | Some cl -> krivine (cl, stack)
        (* If the variable is unbound, we raise an exception *)
        | None -> failwith ("Unbound variable: " ^ x))
  (* If the closure is a lambda abstraction, we return the closure as is *)
  | (Closure(Abs(x, e), env), cl::cs) ->
      krivine (Closure(e, (x, cl)::env), cs)
  (* Pattern matching for the case when the closure is an application of two expressions. *)
  | (Closure(App(e1, e2), env), stack) ->
    (* The first expression is expected to evaluate to a function. *)
      let func = krivine (Closure(e1, env), []) in
      (* We match the function closure to extract the lambda abstraction and the function environment.*)
      (* We then evaluate the second expression and bind it to the variable in the lambda abstraction.*)
      (* Finally, we evaluate the body of the lambda abstraction with the new environment. *)
      begin match func with
        | Closure(Abs(arg, body), fenv) -> krivine (Closure(body, (arg, Closure(e2, env))::fenv), stack)
        (* If the function is not a lambda abstraction, we raise an exception. *)
        | _ -> failwith "Application to non-function"
      end
  (* Pattern matching for the case when the closure is a binary operation. *)
  | (Closure(Plus(e1, e2) | Minus(e1, e2) | Times(e1, e2) | Divide(e1, e2)| Mod(e1, e2) | Equal(e1, e2) | Gt(e1, e2) | Lt(e1, e2) | Gte(e1, e2) | Lte(e1, e2) | Neq(e1, e2) as op, env), stack) ->   (* Binary operations *)
  (* We evaluate the two expressions and match the operation to perform the corresponding operation. *)
      let Closure(Num n1, _) = krivine (Closure(e1, env), stack) in
      let Closure(Num n2, _) = krivine (Closure(e2, env), stack) in
      (* We perform the operation and return the result as a closure. *)
      let result = match op with
      (* We perform the operation and return the result as a closure. *)
        | Plus(_, _) -> n1 + n2
        | Minus(_, _) -> n1 - n2
        | Times(_, _) -> n1 * n2
        | Divide(_, _) -> if n2 = 0 then failwith "Division by zero" else n1 / n2
        | Mod(_, _) -> n1 mod n2
        | Equal(_, _) -> if n1 = n2 then 1 else 0
        | Gt(_, _) -> if n1 > n2 then 1 else 0
        | Lt(_, _) -> if n1 < n2 then 1 else 0
        | Gte(_, _) -> if n1 >= n2 then 1 else 0
        | Lte(_, _) -> if n1 <= n2 then 1 else 0
        | Neq(_, _) -> if n1 != n2 then 1 else 0
        (* If the operation is not supported, we raise an exception. *)
        | _ -> failwith "Unsupported operation"
        (* We return the result as a closure. *)
      in Closure(Num result, env)
  (* Pattern matching for the case when the closure is a boolean value. *)
  | (Closure(T, _), _) -> Closure(Num 1, [])
  | (Closure(F, _), _) -> Closure(Num 0, [])
  (* Pattern matching for the case when the closure is a number. *)
  | (closure, []) -> closure
  (* If the closure is not matched by any of the above cases, we raise an exception. *)
  | _ -> failwith "Unhandled expression or configuration"

(* Function to run the krivine machine on an expression *)
let run_krivine exp =
  (* We start the evaluation with the expression and an empty environment and stack. *)
  let result = krivine (Closure(exp, []), []) in
  match result with
  (* We print the result of the evaluation. *)
  | Closure(Num n, _) -> Printf.printf "Result: Num %d\n" n
  (* If the result is not a number or a boolean, we print other. *)
  | _ -> Printf.printf "Result: Other\n"


















































  (* sir testcase1 *)
  (* CLtype(Var("z"), [(Var("z"),CLtype(Int(3), []))]);; *)
  let test_case1 =
    let env = [("z", Closure(Num 3, []))] in
    let expr = Var("z") in
    run_krivine expr

  (* sir testcase2 *)
  (* CLtype( Add(Add(Int(2),Int(3)),Add(Int(2),Int(3))), []);; *)
  let test_case2 =
    let expr = Plus(Plus(Num 2, Num 3), Plus(Num 2, Num 3)) in
    run_krivine expr

  (* sir testcase3 *)
  (* CLtype(App(Abs("x",Add(Var("x"),Int(1))),Int(2)),[]);; *)
  let test_case3 =
    let expr = App(Abs("x", Plus(Var "x", Num 1)), Num 2) in
    run_krivine expr

  (* sir testcase4 *)
  (* CLtype(App(Abs("x", Mul(Var("x"),Add(Var("x"),Int(1)))),Int(2)),[]);; *)
  let test_case4 =
    let expr = App(Abs("x", Times(Var "x", Plus(Var "x", Num 1))), Num 2) in
    run_krivine expr

  (* sir testcase5 *)
  (* CLtype(App(Abs("x", App(Abs("d",Mul(Var("d"),Int(2))),Int(2))),Int(2)),[]);; *)
  let test_case5 =
    let expr = App(Abs("x", App(Abs("d", Times(Var "d", Num 2)), Num 2)), Num 2) in
    run_krivine expr

  (* sir testcase6 *)
  (* CLtype(Ifthenelse(Grt(Int(8),Int(2)),App(Abs("x", Div(Var("x"),Int(2))),Int(2)),App(Abs("x", Mul(Var("x"),Add(Var("x"),Int(1)))),Int(2))),[]);; *)
  let test_case6 =
    let expr = Ifthenelse(Gt(Num 8, Num 2), App(Abs("x", Divide(Var "x", Num 2)), Num 2), App(Abs("x", Times(Var "x", Plus(Var "x", Num 1))), Num 2)) in
    run_krivine expr

  (* sir testcase7 *)
  (* CLtype(Ifthenelse(Grt(Int(8),Int(2)),Add(Int(1), Int(2)), Div(Int(9), Int(0))),[]);; *)
  let test_case7 =
    let expr = Ifthenelse(Gt(Num 8, Num 2), Plus(Num 1, Num 2), Divide(Num 9, Num 0)) in
    run_krivine expr