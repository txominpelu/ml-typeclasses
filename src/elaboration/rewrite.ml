open XAST
open Name
open Types

type method_definition = {
  (* TODO: How to ensure that his name is not captured *)
  param_name : string; (* Name of the param that contains the def of the dictionary *)
  to_rewrite : string (* Name of the method whose calls will be rewritten *)
}
(**
 * Rewrites the calls to a given overloaded method
 *
 * e.g
 * - a method equal ['a] x y  where equal has type Equal ['a] -> 'a -> 'a -> boolean
 * - is replaced by equal ['a] eqX x y : boolean
 *
 * @param method { name; params; param_type }
 * @param expression ast where the method call will be replaced
 *
 *
 **)
let rec rewrite overl_symbol : expression -> expression = function
  | EVar (_, _, _) as var -> var
  | ELambda (pos, b, e') -> ELambda(pos, b, rewrite overl_symbol e')
  | EApp (pos, (EVar(_, Name name, t) as a), b) when name = overl_symbol.to_rewrite ->
    let newa = EApp(pos, a, EVar(pos, Name overl_symbol.param_name, [])) in
    EApp(pos, newa, rewrite overl_symbol b)
  | EApp (pos, a, b) -> EApp (pos, rewrite overl_symbol a, rewrite overl_symbol b)
  | EBinding (pos, vb, e) -> EBinding (pos, vb, rewrite overl_symbol e)
  | EForall (pos, tvs, e) -> EForall(pos, tvs, rewrite overl_symbol e)
  | ETypeConstraint (pos, e, xty) -> ETypeConstraint (pos, rewrite overl_symbol e, xty)
  | EExists (pos , t, e) -> EExists (pos, t, rewrite overl_symbol e)
  | EDCon (pos, name, tys, es) -> EDCon (pos, name, tys, List.map (rewrite overl_symbol) es)
  | EMatch (pos, s, bs) -> EMatch (pos, rewrite overl_symbol s, bs)
  | ERecordAccess (pos, e, l) -> ERecordAccess (pos, rewrite overl_symbol e, l)
  | ERecordCon (pos, n, i, []) -> assert false
  | other -> other

let class_type_name p_name = TName (String.lowercase p_name)

(**
 * Rewrites the calls to all the overloaded symbols of a class in a term
 **)
let rewrite_all_labels class_members term =
  List.fold_left ( function acc -> function (_, LName lname, _) ->
    let param_name = (String.uncapitalize lname) ^ "X" in
    rewrite { param_name = param_name; to_rewrite = lname } acc
  ) term class_members

let wrap_with_function pos term = function
  | ClassPredicate (TName pred_type, pred_name )  ->
    let t = TyApp (pos, class_type_name pred_type, [TyVar (pos, pred_name)]) in
    let name = (String.uncapitalize pred_type)^"X" in
    ELambda (pos, (Name name, t), term)

(**
  * Rewrites a term that depends on an a dictionary.
  * e.g
  * - The term: let rec ['a ] [Hashable 'a] (search: 'a -> int) = ['a] fun (x: 'a) -> hash['a] x[]
  * - to: let rec ['a] (search: 'a hashable -> 'a -> int) = ['a] fun (hashX : 'a hashable) -> fun (x: 'a) -> hash['a] x[]
  *   giving the term the type: 'a hashable -> 'a -> int
  *
  * Basically it just adds another function that injects the dictionary and changes the type of the function.
  *
  * Note: After calling this method its still necessary to replace calls to overloaded symbols:
  * in the example hash['a] x[] still needs to be replaced by hash['a] hashX[] x[] (this needs to be done with rewrite)
**)

let replace_term_def = function
    | ValueDef(pos, param_types, class_predicates, (val_name, t), expr) when List.length class_predicates > 0 ->
      let new_type = List.map (function
        | ClassPredicate(TName pred_type, pred_name) ->
          TyApp(pos, class_type_name pred_type, [TyVar(pos, pred_name)])
        ) class_predicates in
      let EForall (_, [params], left) = expr in
      let new_expr = List.fold_left (function term -> wrap_with_function pos term) left class_predicates in
      let t_out = TyApp(pos, TName "->", new_type@[t]) in
      ValueDef(pos, param_types, [], (val_name, t_out), EForall (pos, param_types , new_expr))
    | v_def -> v_def

(* Still to do, for every label in every class in class_predicates rewrite the overloaded_symbol in term *)
