open Positions
open Name
open XAST
open Types
open ElaborationExceptions

(**
 * For example the class_definition:
 * class Hashable 'a { hash : 'a -> int }
 *
 * Adds the following to the environment (not included: let hash ['a] (hashA : hashable ['a]) : a' -> int = hashA.hash ):
 *
 * classes => [(hashable,(KArrow(KStar, KStar),TypeDef(_,KArrow(KStar, KStar), hashable, DRecordType(['a], (hash, TyApp(->, TyVar('a),TyApp(int, )))))))]
 *
 * types => (hashable,(KArrow(KStar, KStar),TypeDef(_,KArrow(KStar, KStar), hashable, DRecordType(['a], (hash, TyApp(->, TyVar('a),TyApp(int, )))))))
 *
 * labels => [(hash,(['a],TyApp(->, TyVar('a),TyApp(int, )),hashable))]
 *)
type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames (* param types*) * Types.t (*kind*) * tname (*class*))) list;
}

let empty = { values = []; types = []; classes = []; labels = [] }

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

(**
 * Adds a value of a ADT to the environment.
 *
 * @param x name (e.g. Nil)
 * @param ts variables of the polymorphic type e.g. [Name.TName "'a"]
 * @param ty type (e.g Types.TyApp (<abstr>, Name.TName "list",
 *    [Types.TyVar (<abstr>, Name.TName "'a")]))
 * @param env environment
 *)
let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

(**
 * Adds the type (name, (kind, ast definition)) to the environment.
 *
 * @param t name
 * @param kind kind of the type
 *    (e.g list : KArrow (KStar, KStar) gets a non-polymorph type and returns a non-polymorph type)
 * @param tdef ast definition of the type
 * @env env current environment
 *)
let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)

let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k, c) :: env.classes }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let is_superclass pos k1 k2 env =
  (* Student! This is your job! *)
  true

(** Creates an empty type variable that will be added to the environment
 * for the given name (one use is to typecheck polymorphic types, since
 * we want to check them we need to ar their Var type variables to the env.)
 *
 * @param t name of the variable
 * @param env environment
 *)
let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]

let string_of_env_values { values; _ } =
    (string_of_list (fun (tnames, bind) -> Printf.sprintf "(%s,%s)" (string_of_tnames tnames) (string_of_binding bind)) values)

let string_of_env_types { types; _ } =
    (string_of_list (fun (tname, (kind, type_def))-> Printf.sprintf "(%s,(%s,%s))" (string_of_tname tname) (string_of_kind kind) (string_of_type_definition type_def)) types)

let string_of_env_classes { classes; _ } =
    (string_of_list (fun (tname, class_def)-> Printf.sprintf "(%s,%s)" (string_of_tname tname) (string_of_class_definition class_def)) classes)

let string_of_env_labels { labels; _ } =
    (string_of_list (fun (LName lname, (tnames, mltype, TName tname))-> Printf.sprintf "(%s,(%s,%s,%s))" lname (string_of_tnames tnames) (string_of_t mltype) tname) labels)

(*type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
}*)
let string_of_env env  =
  let { values; types; classes; labels } = env in
  Printf.sprintf "{ values = %s; types = %s; classes = %s; labels = %s }"
    (string_of_env_values env)
    (string_of_env_types env)
    (string_of_env_classes env)
    (string_of_env_labels env)
