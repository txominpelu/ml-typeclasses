(** This module transforms a program with implicit dictionaries into a
    program with explicit dictionary passing. *)

(** [program p] is [p] with explicit dictionary passing. *)
val program : XAST.program -> XAST.program

val block : ElaborationEnvironment.t ->
             XAST.block -> XAST.block list * ElaborationEnvironment.t

val type_definition : ElaborationEnvironment.t ->
             XAST.type_definition -> ElaborationEnvironment.t
