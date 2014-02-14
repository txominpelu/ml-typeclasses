(** This module transforms a program with implicit dictionaries into a
    program with explicit dictionary passing. *)

(** [program p] is [p] with explicit dictionary passing. *)
val program : XAST.program -> XAST.program

val block : ElaborationEnvironment.t ->
             XAST.block -> XAST.block list * ElaborationEnvironment.t

val value_binding : ElaborationEnvironment.t ->
             XAST.value_binding -> XAST.value_binding * ElaborationEnvironment.t

val type_definition : ElaborationEnvironment.t ->
             XAST.type_definition -> ElaborationEnvironment.t

val eforall : Positions.position ->
           XAST.tnames -> XAST.expression -> XAST.expression

val expression : ElaborationEnvironment.t ->
           XAST.expression -> XAST.expression * XAST.mltype
