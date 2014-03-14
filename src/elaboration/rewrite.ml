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
let rec rewrite overl_symbol typecheck: expression -> expression = function
  | EVar (_, _, _) as var -> var
  | ELambda (pos, b, e') -> ELambda(pos, b, rewrite overl_symbol typecheck e')
  | EApp (pos, (EVar(_, Name name, t) as a), b) when name = overl_symbol.to_rewrite ->
    let (_, t) = typecheck a in
    print_string "\nType:\n";
    print_string (string_of_t t);
    print_string "\n";
    let newa = EApp(pos, a, EVar(pos, Name overl_symbol.param_name, [])) in
    EApp(pos, newa, rewrite overl_symbol typecheck b)
  | EApp (pos, a, b) -> EApp (pos, rewrite overl_symbol typecheck a, rewrite overl_symbol typecheck b)
  | EBinding (pos, vb, e) -> EBinding (pos, vb, rewrite overl_symbol typecheck e)
  | EForall (pos, tvs, e) -> EForall(pos, tvs, rewrite overl_symbol typecheck e)
  | ETypeConstraint (pos, e, xty) -> ETypeConstraint (pos, rewrite overl_symbol typecheck e, xty)
  | EExists (pos , t, e) -> EExists (pos, t, rewrite overl_symbol typecheck e)
  | EDCon (pos, name, tys, es) -> EDCon (pos, name, tys, List.map (rewrite overl_symbol typecheck) es)
  | EMatch (pos, s, branches) ->
    let rewritten_branches = List.map ( function Branch(pos2, pattern, expr) ->
      Branch(pos2, pattern, rewrite overl_symbol typecheck expr)
    ) branches in
    EMatch (pos, rewrite overl_symbol typecheck s, rewritten_branches)
  | ERecordAccess (pos, e, l) -> ERecordAccess (pos, rewrite overl_symbol typecheck e, l)
  | ERecordCon (pos, n, i, []) -> assert false
  | ERecordCon (pos, n, i, record_bindings) ->
    let rewritten_bindings = List.map ( function RecordBinding(l, expr) ->
      RecordBinding(l, rewrite overl_symbol typecheck expr)
    ) record_bindings in
    ERecordCon (pos, n, i, rewritten_bindings)
  | other -> other

let class_type_name p_name = TName (String.lowercase p_name)

(**
 * Rewrites the calls to all the overloaded symbols of a class in a term
 **)
let rewrite_all_labels class_members class_name term typecheck =
  List.fold_left ( function acc -> function (_, LName lname, _) ->
    let param_name = (String.uncapitalize class_name) ^ "X" in
    rewrite { param_name = param_name; to_rewrite = lname } typecheck acc
  ) term class_members

let wrap_with_function pos term = function
  | ClassPredicate (TName pred_type, pred_name )  ->
    let t = TyApp (pos, class_type_name pred_type, [TyVar (pos, pred_name)]) in
    let name = (String.uncapitalize pred_type)^"X" in
    ELambda (pos, (Name name, t), term)
