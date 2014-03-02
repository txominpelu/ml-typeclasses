open String
open Name
open XAST
open Types
open Positions
open Rewrite
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))


let rec program p = handle_error List.(fun () ->
  flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
)

and block env = function
  | BTypeDefinitions (TypeDefs(_, type_defs) as ts) ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let newd = match d with
    |  BindValue(pos, v_def) -> BindValue (pos, List.map replace_term_def v_def)
    |  BindRecValue(pos, v_def) -> BindRecValue (pos, List.map replace_term_def v_def)
    |  other -> other in
    let d, env = value_binding env newd in
    ([BDefinition d], env)

  | BClassDefinition c ->
    (** Class definitions are ignored. Student! This is your job! *)
    (* Conditions:
      * - There's no other class/instance with the same name:
      *      (already verified by bind_class)
      * - There's no cycles between classes (eg no K1 > K2 > ... > K1)
      * - The superclasses of a class are independent in the typing context
      *   (if class K1 a K2 a ... => K a, then there's no Ki < Kj)
      * - An overloaded symbol cannot be declared twice in the same class
      * - An overloaded symbol can only be declared in one class
      * - The types of the overloaded symbols must be closed with respect to alpha
      * - The instances of a class must declare all the methods of the class
      * - For the instance of a class with a superclass there needs to be
      *   an instance for the superclass with the same alpha defined
      * - All parent classes exist
      **)
    let mutual_defs = elaborate_class_def c in
    let env1 = type_definitions env mutual_defs in
    let env2 = bind_class c.class_name c env1 in
    let defs = List.map (elaborate_class_member c) c.class_members in
    let (defs_binded, newenv) = (Misc.list_foldmap value_binding env2 defs) in
    let bdefs = List.map (fun x -> BDefinition x) defs_binded in
    ((BTypeDefinitions mutual_defs) :: bdefs, newenv)

  | BInstanceDefinitions is ->
    (** Instance definitions are ignored. Student! This is your job! *)
    (* look if there's a class defined for every given instance
     * - The instances of a class must declare all the methods of the class
     * check for repeated instances of the same class for the same type *)
    let instances_elab = List.map (fun x -> elaborate_instance_def x env) is in
    let (instances_binded, newenv) = (Misc.list_foldmap value_binding env instances_elab) in
    let definitions = List.map (function elab -> BDefinition elab) instances_binded in
    List.map (fun { instance_position; instance_class_name ; _ } -> lookup_class instance_position instance_class_name env) is;
    (definitions , newenv)
    (*([BInstanceDefinitions is] , newenv)*)

 and elaborate_instance_def instance_def env =
  let generate_instance_name class_name index = Name ((String.uncapitalize class_name)^(String.capitalize index)) in
  let { instance_parameters; instance_typing_context; instance_class_name; instance_index; instance_members; instance_position } = instance_def in
  let TName i_class_name = instance_class_name in
  let TName i_index = instance_index in
  let kind = build_record_kind instance_position (TName i_class_name) (TName i_index) instance_parameters in
  let record_name = generate_instance_name i_class_name i_index in
  let record_noparam = ERecordCon(instance_position, record_name, [TyApp(instance_position, instance_index, [])], instance_members) in
  let record = EForall (instance_position, instance_parameters, record_noparam) in
  let r =  ValueDef(instance_position, instance_parameters, instance_typing_context, (record_name,kind),record) in
  let last = replace_term_def r in
  print_string "ValueDef:\n";
  print_string (string_of_value_def last);
  let ValueDef(_, _, _, _, expr) = last in
  print_string "Expression:\n";
  print_string (ASTio.to_string ASTio.XAST.pprint_expression record);
  print_string "\n";
  print_string "Expression:\n";
  print_string (ASTio.to_string ASTio.XAST.pprint_expression expr);
  print_string "\n";
  BindValue(instance_position, [last])


and build_record_kind pos class_name instance_index instance_parameters =
  let TName i_class_name = class_name in
  let params = List.map (fun x -> TyVar(pos, x)) instance_parameters in
  TyApp(pos, TName (String.lowercase i_class_name), [TyApp(pos, instance_index, params)])

and elaborate_class_def c =
  let datatype_def = DRecordType ([c.class_parameter], c.class_members)  in
  let TName (class_name_string) = c.class_name in
  let type_name = TName (String.lowercase class_name_string) in
  let type_defs = [TypeDef (c.class_position, (KArrow (KStar, KStar)), type_name, datatype_def)] in
    TypeDefs (c.class_position, type_defs)

and elaborate_class_member cl (member_pos, LName m_name, member_type)  =
  let TName c_name = cl.class_name in
  let type_name = String.lowercase c_name in
  let expression = EForall (member_pos, [cl.class_parameter], ELambda(member_pos,
		(Name.Name "x", TyApp(member_pos, TName type_name,
                                      [TyVar(member_pos, cl.class_parameter)])),
                ERecordAccess (member_pos, EVar (member_pos, Name.Name "x", []), LName m_name))) in
  let member_def = ValueDef(member_pos, [cl.class_parameter], [],
                            (Name m_name,TyApp(member_pos, TName "->",
                              [TyApp(member_pos, TName type_name, [TyVar(member_pos,cl.class_parameter)]);
                               member_type])), expression) in
  BindValue(member_pos, [member_def])

and type_definitions env (TypeDefs (_, tdefs)) =
  (* Generates an environment for the givent type_defs *)
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    (* adds a type to the environment of types *)
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

(**
  * Checks
  * - if the type is not polymorphic if the type passed
  *   has the same type as the type of the same name found
  *   found in the environment
  * - if the type is polymorphic verifies recursively that
  *   the type is equal to the type stored in the environment
  *   considering the variable types.
*)
and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, (TName tname as t), tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ ->
    raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs = List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with _ ->
    raise (InvalidTypeApplication pos)

and expression env = function
  | EVar (pos, ((Name s) as x), tys) ->
    (EVar (pos, x, tys), type_application pos env x tys)

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)


  | EApp (pos, a, b) ->
    (*print_string "Type a:\n";
    print_string (string_of_t a_ty);
    print_string "Expression:\n";
    print_string (ASTio.to_string ASTio.XAST.pprint_expression a);
    print_string "\n";*)
    let a, a_ty = expression env a in
    let b, b_ty = expression env b in
    print_string "\nEnvironment:\n";
    print_string (string_of_env env);
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
          (* TODO: make naming standards explicit e.g type for class = String.uncapitalize*)
          (* FIXME: ensure fresh name*)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end
  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ -> raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty'
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, _) = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme x ts ty env in
    (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
    | ts, EForall (pos, [], ((EForall _) as e)) ->
      eforall pos ts e
    | [], EForall (pos, [], e) ->
      e
    | [], EForall (pos, _, _) ->
      raise (InvalidNumberOfTypeAbstraction pos)
    | [], e ->
      e
    | x :: xs, EForall (pos, t :: ts, e) ->
      if x <> t then
        raise (SameNameInTypeAbstractionAndScheme pos);
      eforall pos xs (EForall (pos, ts, e))
    | _, _ ->
      raise (InvalidNumberOfTypeAbstraction pos)


and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env' = introduce_type_parameters env ts in
  check_wf_scheme env ts xty;

  if is_value_form e then begin
    let e = eforall pos ts e in
    let e, ty = expression env' e in
    let b = (x, ty) in
    check_equal_types pos xty ty;
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme x ts ty env)
  end else begin
    if ts <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  bind_scheme x ts ty env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false
