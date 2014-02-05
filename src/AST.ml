open Name
open Positions
open Types

module Make (P : Types.TypingSyntax) = struct

  include P

  type program = block list


  and block =
    | BClassDefinition of class_definition
    | BInstanceDefinitions of instance_definition list
    | BTypeDefinitions of type_mutual_definitions
    | BDefinition of value_binding

  and class_definition = {
    class_position  : position;
    class_parameter : tname;
    superclasses    : tname list;
    class_name      : tname;
    class_members   : (position * lname * mltype) list;
  }

  and instance_definition = {
    instance_position       : position;
    instance_parameters     : tname list;
    instance_typing_context : class_predicate list;
    instance_class_name     : tname;
    instance_index          : tname;
    instance_members        : record_binding list;
  }

  and value_binding =
    | BindValue of position * value_definition list
    | BindRecValue of position * value_definition list
    | ExternalValue of position * tnames * binding * string


  and type_mutual_definitions =
    | TypeDefs of position * type_definition list

  and expression =

    (** Core ML. *)
    | EVar of position * name * instantiation
    | ELambda of position * binding * expression
    | EApp of position * expression * expression
    | EBinding of position * value_binding * expression
    | EPrimitive of position * primitive

    (** Type annotations. *)
    | EForall of position * tname list * expression
    | EExists of position * tname list * expression
    | ETypeConstraint of position * expression * mltype

    (** Algebraic datatypes. *)
    | EDCon of position * dname * instantiation * expression list
    | EMatch of position * expression * branch list

    (** Records. *)
    | ERecordAccess of position * expression * lname
    | ERecordCon of position * name * instantiation * record_binding list

  (** Constant. *)
  and primitive =
    | PIntegerConstant of int     (** Integer constant. *)
    | PCharConstant of char       (** Character constant. *)
    | PUnit                       (** Unit constant. *)

  (** Pattern matching branch. *)
  and branch =
    | Branch of position * pattern * expression

  and record_binding =
    | RecordBinding of lname * expression

  and type_definition =
    | TypeDef of position * mltypekind * tname * datatype_definition
    | ExternalType of position * tnames * tname * string

  and datatype_definition =
    | DAlgebraic of (position * dname * tnames * mltype) list
    | DRecordType of tnames * (position * lname * mltype) list

  (** A value definition consists of a list of explicit universal
      quantifiers, a binding, and an expression. *)
  and value_definition =
    | ValueDef of position * tnames * class_predicates * binding * expression

  and pattern =
    | PVar of position * name
    | PWildcard of position
    | PAlias of position * name * pattern
    | PTypeConstraint of position * pattern * mltype
    | PPrimitive of position * primitive
    | PData of position * dname * instantiation * pattern list
    | PAnd of position * pattern list
    | POr of position * pattern list

  and tnames = tname list

  and mltype = Types.t

  and mltypescheme = Types.scheme

  and mltypekind = Types.kind

  let string_of_name name = match name with Name sName -> sName ;;

  let string_of_tname tname = match tname with TName name -> name ;;

  let string_of_tnames typeNames = String.concat " " (List.map string_of_tname typeNames) ;;

  let string_of_class_predicate predicate = match predicate with ClassPredicate (name1, name2) ->
    Printf.sprintf "Classname(%s,%s)" (string_of_tname name1) (string_of_tname name2) ;;

  let string_of_class_predicates cl_predicates = String.concat " " (List.map
  string_of_class_predicate cl_predicates) ;;

  let string_of_value_def = function
    | ValueDef (position, tnames, class_predicates, binding ,expression) ->
        Printf.sprintf "ValueDef(_, %s, %s, binding, expression)"
        (string_of_tnames tnames)
        (string_of_class_predicates class_predicates) ;;

  let string_of_value_binding = function
    | BindValue (pos, value_defs) -> Printf.sprintf "BindValue(_, %s)"
    (String.concat " " (List.map string_of_value_def value_defs))
    | BindRecValue (pos, value_defs) -> Printf.sprintf "BindRecValue(_,%s)"
    (String.concat " " (List.map string_of_value_def value_defs))
    | ExternalValue (pos, tnames, binding, str) -> "ExternalValue(_, tnames, binding, string)";;

  let string_of_block = function
    | BClassDefinition class_def -> "BClassDefinition(classDef)"
    | BInstanceDefinitions instances -> "BInstanceDefinition(instances: List)"
    | BTypeDefinitions mutual_defs -> "BTypeDefintions(mutual_defs)"
    | BDefinition value_bind-> Printf.sprintf "BDefinition(%s)"
    (string_of_value_binding value_bind);;

  let string_of_datatype_definition = function
    | DAlgebraic alg ->
      let inside = String.concat "|"
      (List.map
         (fun (_, DName dname, tnames, mltype) ->
           Printf.sprintf "(%s, %s, %s)"
             dname
             (string_of_tnames tnames)
             (string_of_t mltype)
         )  alg
      ) in
      Printf.sprintf "DAlgebraic(%s)" inside
    | DRecordType (tnames, record) ->
      let inside = String.concat ";"
      (List.map
         (fun (_, LName lname, mltype) ->
           Printf.sprintf "(%s, %s)"
             lname
             (string_of_t mltype)
         )  record
      ) in
      Printf.sprintf "DRecordType(%s, %s)" (string_of_tnames tnames) inside

  let string_of_type_definition = function
    | TypeDef (_ , mltypekind , tname , datatype_definition) ->
      Printf.sprintf "TypeDef(_,%s, %s, %s)" (string_of_kind mltypekind) (string_of_tname tname) (string_of_datatype_definition datatype_definition)
    | ExternalType (_ , tnames , tname , t) ->
      Printf.sprintf "ExternalType(_, %s,%s, %s)" (string_of_tnames tnames) (string_of_tname tname) t




end

module Generic = Make (struct
  type binding
  let binding _ _ = assert false
  let destruct_binding _ = assert false
  type instantiation
  let instantiation _ _ = assert false
  let destruct_instantiation_as_type_applications _ = assert false
  let destruct_instantiation_as_type_constraint _ = assert false
end)

module type GenericS = module type of Generic
