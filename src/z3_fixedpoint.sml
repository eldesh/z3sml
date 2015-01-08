
structure Z3_Fixedpoint =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_fixedpoint   = unit ptr
  type Z3_context      = unit ptr
  type Z3_symbol       = unit ptr
  type Z3_ast          = unit ptr
  type Z3_func_decl    = unit ptr
  type Z3_params       = unit ptr
  type Z3_param_descrs = unit ptr
  type Z3_ast_vector   = unit ptr
  type Z3_string       = string
  type Z3_stats        = unit ptr
  type Z3_lbool        = Z3_enum.Z3_lbool

  val Z3_mk_fixedpoint =
    Dyn.dlsym(libz3, "Z3_mk_fixedpoint")
    : _import Z3_context -> Z3_fixedpoint

  val Z3_fixedpoint_inc_ref =
    Dyn.dlsym(libz3, "Z3_fixedpoint_inc_ref")
    : _import (Z3_context, Z3_fixedpoint) -> ()

  val Z3_fixedpoint_dec_ref =
    Dyn.dlsym(libz3, "Z3_fixedpoint_dec_ref")
    : _import (Z3_context, Z3_fixedpoint) -> ()

  val Z3_fixedpoint_add_rule =
    Dyn.dlsym(libz3, "Z3_fixedpoint_add_rule")
    : _import (Z3_context, Z3_fixedpoint, Z3_ast, Z3_symbol) -> ()

  val Z3_fixedpoint_add_fact =
    Dyn.dlsym(libz3, "Z3_fixedpoint_add_fact")
    : _import (Z3_context, Z3_fixedpoint, Z3_func_decl, word, word array) -> ()

  val Z3_fixedpoint_assert =
    Dyn.dlsym(libz3, "Z3_fixedpoint_assert")
    : _import (Z3_context, Z3_fixedpoint, Z3_ast) -> ()

  val Z3_fixedpoint_query =
    Dyn.dlsym(libz3, "Z3_fixedpoint_query")
    : _import (Z3_context, Z3_fixedpoint, Z3_ast) -> Z3_lbool

  fun Z3_fixedpoint_query_relations (c, d, relations) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_fixedpoint_query_relations"))
    ( c : Z3_context
    , d : Z3_fixedpoint
    , Vector.length relations : int
    , relations : Z3_func_decl vector) : Z3_lbool

  val Z3_fixedpoint_get_answer =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_answer")
    : _import (Z3_context, Z3_fixedpoint) -> Z3_ast

  val Z3_fixedpoint_get_reason_unknown =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_fixedpoint_get_reason_unknown")
     : _import (Z3_context, Z3_fixedpoint) -> char ptr)

  val Z3_fixedpoint_update_rule =
    Dyn.dlsym(libz3, "Z3_fixedpoint_update_rule")
    : _import (Z3_context, Z3_fixedpoint, Z3_ast, Z3_symbol) -> ()

  val Z3_fixedpoint_get_num_levels =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_num_levels")
    : _import (Z3_context, Z3_fixedpoint, Z3_func_decl) -> word

  val Z3_fixedpoint_get_cover_delta =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_cover_delta")
    : _import (Z3_context, Z3_fixedpoint, int, Z3_func_decl) -> Z3_ast

  val Z3_fixedpoint_add_cover =
    Dyn.dlsym(libz3, "Z3_fixedpoint_add_cover")
    : _import (Z3_context, Z3_fixedpoint, int, Z3_func_decl, Z3_ast) -> ()

  val Z3_fixedpoint_get_statistics =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_statistics")
    : _import (Z3_context, Z3_fixedpoint) -> Z3_stats

  val Z3_fixedpoint_register_relation =
    Dyn.dlsym(libz3, "Z3_fixedpoint_register_relation")
    : _import (Z3_context, Z3_fixedpoint, Z3_func_decl) -> ()

  fun Z3_fixedpoint_set_predicate_representation (c, d, f, relation_kinds) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_fixedpoint_set_predicate_representation"))
    ( c : Z3_context
    , d : Z3_fixedpoint
    , f : Z3_func_decl
    , Vector.length relation_kinds : int
    , relation_kinds : Z3_symbol vector) : ()

(* undefined symbols? *)
(*
  val Z3_fixedpoint_get_rules =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_rules")
    : _import (Z3_context, Z3_fixedpoint) -> Z3_ast_vector

  val Z3_fixedpoint_get_assertions =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_assertions")
    : _import (Z3_context, Z3_fixedpoint) -> Z3_ast_vector
    *)

  val Z3_fixedpoint_set_params =
    Dyn.dlsym(libz3, "Z3_fixedpoint_set_params")
    : _import (Z3_context, Z3_fixedpoint, Z3_params) -> ()

  val Z3_fixedpoint_get_help =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_fixedpoint_get_help")
     : _import (Z3_context, Z3_fixedpoint) -> char ptr)

  val Z3_fixedpoint_get_param_descrs =
    Dyn.dlsym(libz3, "Z3_fixedpoint_get_param_descrs")
    : _import (Z3_context, Z3_fixedpoint) -> Z3_param_descrs

  fun Z3_fixedpoint_to_string (c, f, queries) =
    Ptr.importString(
      _ffiapply (Dyn.dlsym(libz3, "Z3_fixedpoint_to_string"))
      ( c : Z3_context
      , f : Z3_fixedpoint
      , Array.length queries : int
      , queries : Z3_ast array) : char ptr)

  val Z3_fixedpoint_from_string =
    Dyn.dlsym(libz3, "Z3_fixedpoint_from_string")
    : _import (Z3_context, Z3_fixedpoint, Z3_string) -> Z3_ast_vector

  val Z3_fixedpoint_from_file =
    Dyn.dlsym(libz3, "Z3_fixedpoint_from_file")
    : _import (Z3_context, Z3_fixedpoint, Z3_string) -> Z3_ast_vector

  val Z3_fixedpoint_push =
    Dyn.dlsym(libz3, "Z3_fixedpoint_push")
    : _import (Z3_context, Z3_fixedpoint) -> ()

  val Z3_fixedpoint_pop =
    Dyn.dlsym(libz3, "Z3_fixedpoint_pop")
    : _import (Z3_context, Z3_fixedpoint) -> ()

  val Z3_fixedpoint_init =
    Dyn.dlsym(libz3, "Z3_fixedpoint_init")
    : _import (Z3_context, Z3_fixedpoint, unit ptr) -> ()

(*
  val Z3_fixedpoint_set_reduce_assign_callback =
    Dyn.dlsym(libz3, "Z3_fixedpoint_set_reduce_assign_callback")
    : _import (Z3_context, Z3_fixedpoint, (unit ptr, Z3_func_decl, word, Z3_ast vector, word, Z3_ast vector) -> ()) -> ()
    *)

(*
  val Z3_fixedpoint_set_reduce_app_callback =
    Dyn.dlsym(libz3, "Z3_fixedpoint_set_reduce_app_callback")
    : _import (Z3_context, Z3_fixedpoint, (unit ptr, Z3_func_decl, word, Z3_ast vector, Z3_ast ref)->()) -> ()
    *)

end (* local *)
end


