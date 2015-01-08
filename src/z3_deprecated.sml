
(**
 * Deprecated APIs.
 *)
structure Z3_Deprecated =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context  = unit ptr
  type Z3_model    = unit ptr
  type Z3_ast      = unit ptr
  type Z3_symbol   = unit ptr
  type Z3_sort     = unit ptr
  type Z3_lbool    = Z3_enum.Z3_lbool
  type Z3_bool     = int
  type Z3_string   = String.string
  type Z3_literals = unit ptr
  type Z3_func_decl = unit ptr
  type Z3_solver    = unit ptr
  type Z3_error_code = Z3_enum.Z3_error_code

  (*
   * Deprecated Injective functions API
   *)
  fun Z3_mk_injective_function (c, s, domain, range) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_injective_function"))
    ( c : Z3_context
    , s : Z3_symbol
    , Vector.length domain : int
    , domain : Z3_sort vector
    , range : Z3_sort) : Z3_func_decl

  (*
   * Deprecated Constraints API
   *)
  val Z3_set_logic =
    Dyn.dlsym (libz3, "Z3_set_logic")
    : _import (Z3_context, Z3_string) -> Z3_bool

  val Z3_push =
    Dyn.dlsym (libz3, "Z3_push")
    : _import Z3_context -> ()

  val Z3_pop =
    Dyn.dlsym (libz3, "Z3_pop")
    : _import (Z3_context, word) -> ()

  val Z3_get_num_scopes =
    Dyn.dlsym (libz3, "Z3_get_num_scopes")
    : _import Z3_context -> word

  val Z3_persist_ast =
    Dyn.dlsym (libz3, "Z3_persist_ast")
    : _import (Z3_context, Z3_ast, word) -> ()

  val Z3_assert_cnstr =
    Dyn.dlsym (libz3, "Z3_assert_cnstr")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_check_and_get_model =
    Dyn.dlsym (libz3, "Z3_check_and_get_model")
    : _import (Z3_context, Z3_model ref) -> Z3_lbool

  val Z3_check =
    Dyn.dlsym (libz3, "Z3_check")
    : _import Z3_context -> Z3_lbool

  fun Z3_check_assumptions (c, assumptions, m, proof, core_size, core) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_check_assumptions"))
    ( c : Z3_context
    , Vector.length assumptions : int
    , assumptions : Z3_ast vector
    , m : Z3_model ref
    , proof : Z3_ast ref
    , core_size : word ref
    , core : Z3_ast array) : Z3_lbool

  fun Z3_get_implied_equalities (c, s, terms, class_ids) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_get_implied_equalities"))
    ( c : Z3_context
    , s : Z3_solver
    , Vector.length terms : int
    , terms : Z3_ast vector
    , class_ids : word array) : Z3_lbool

  val Z3_del_model =
    Dyn.dlsym (libz3, "Z3_del_model")
    : _import (Z3_context, Z3_model) -> ()

  (*
   * Deprecated Search control API
   *)
  val Z3_soft_check_cancel =
    Dyn.dlsym (libz3, "Z3_soft_check_cancel")
    : _import Z3_context -> ()

  val Z3_get_search_failure =
    Dyn.dlsym (libz3, "Z3_get_search_failure")
    : _import Z3_context -> Z3_enum.Z3_search_failure 

  (*
   * Deprecated Labels API
   *)
  val Z3_mk_label =
    Dyn.dlsym (libz3, "Z3_mk_label")
    : _import (Z3_context, Z3_symbol, Z3_bool, Z3_ast) -> Z3_ast

  val Z3_get_relevant_labels =
    Dyn.dlsym (libz3, "Z3_get_relevant_labels")
    : _import Z3_context -> Z3_literals

  val Z3_get_relevant_literals =
    Dyn.dlsym (libz3, "Z3_get_relevant_literals")
    : _import Z3_context -> Z3_literals

  val Z3_get_guessed_literals =
    Dyn.dlsym (libz3, "Z3_get_guessed_literals")
    : _import Z3_context -> Z3_literals

  val Z3_del_literals =
    Dyn.dlsym (libz3, "Z3_del_literals")
    : _import (Z3_context, Z3_literals) -> ()

  val Z3_get_num_literals =
    Dyn.dlsym (libz3, "Z3_get_num_literals")
    : _import (Z3_context, Z3_literals) -> word

  val Z3_get_label_symbol =
    Dyn.dlsym (libz3, "Z3_get_label_symbol")
    : _import (Z3_context, Z3_literals, word) -> Z3_symbol

  val Z3_get_literal =
    Dyn.dlsym (libz3, "Z3_get_literal")
    : _import (Z3_context, Z3_literals, word) -> Z3_ast

  val Z3_disable_literal =
    Dyn.dlsym (libz3, "Z3_disable_literal")
    : _import (Z3_context, Z3_literals, word) -> ()

  val Z3_block_literals =
    Dyn.dlsym (libz3, "Z3_block_literals")
    : _import (Z3_context, Z3_literals) -> ()

  (*
   * Deprecated Model API
   *)
  val Z3_get_model_num_constants =
    Dyn.dlsym (libz3, "Z3_get_model_num_constants")
    : _import (Z3_context, Z3_model) -> word

  val Z3_get_model_constant =
    Dyn.dlsym (libz3, "Z3_get_model_constant")
    : _import (Z3_context, Z3_model, word) -> Z3_func_decl

  val Z3_get_model_num_funcs =
    Dyn.dlsym (libz3, "Z3_get_model_num_funcs")
    : _import (Z3_context, Z3_model) -> word

  val Z3_get_model_func_decl =
    Dyn.dlsym (libz3, "Z3_get_model_func_decl")
    : _import (Z3_context, Z3_model, word) -> Z3_func_decl

  val Z3_eval_func_decl =
    Dyn.dlsym (libz3, "Z3_eval_func_decl")
    : _import (Z3_context, Z3_model, Z3_func_decl, Z3_ast ref) -> Z3_bool

  val Z3_is_array_value =
    Dyn.dlsym (libz3, "Z3_is_array_value")
    : _import (Z3_context, Z3_model, Z3_ast, word ref) -> Z3_bool

  val Z3_get_array_value =
    Dyn.dlsym (libz3, "Z3_get_array_value")
    : _import (Z3_context, Z3_model, Z3_ast, word
              , Z3_ast array, Z3_ast array, Z3_ast ref) -> ()

  val Z3_get_model_func_else =
    Dyn.dlsym (libz3, "Z3_get_model_func_else")
    : _import (Z3_context, Z3_model, word) -> Z3_ast

  val Z3_get_model_func_num_entries =
    Dyn.dlsym (libz3, "Z3_get_model_func_num_entries")
    : _import (Z3_context, Z3_model, word) -> word

  val Z3_get_model_func_entry_num_args =
    Dyn.dlsym (libz3, "Z3_get_model_func_entry_num_args")
    : _import (Z3_context, Z3_model, word, word) -> word

  val Z3_get_model_func_entry_arg =
    Dyn.dlsym (libz3, "Z3_get_model_func_entry_arg")
    : _import (Z3_context, Z3_model, word, word, word) -> Z3_ast

  val Z3_get_model_func_entry_value =
    Dyn.dlsym (libz3, "Z3_get_model_func_entry_value")
    : _import (Z3_context, Z3_model, word, word) -> Z3_ast

  val Z3_eval =
    Dyn.dlsym (libz3, "Z3_eval")
    : _import (Z3_context, Z3_model, Z3_ast, Z3_ast ref) -> Z3_bool

  fun Z3_eval_decl (c, m, d, args, v) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_eval_decl"))
    ( c : Z3_context
    , m : Z3_model
    , d : Z3_func_decl
    , Vector.length args : int
    , args : Z3_ast vector
    , v : Z3_ast ref) : Z3_bool

  (*
   * Deprecated String conversion API
   *)
  val Z3_context_to_string =
    Ptr.importString o
    (Dyn.dlsym (libz3, "Z3_context_to_string")
    : _import Z3_context -> char ptr)

  val Z3_statistics_to_string =
    Ptr.importString o
    (Dyn.dlsym (libz3, "Z3_statistics_to_string")
    : _import Z3_context -> char ptr)

  val Z3_get_context_assignment =
    Dyn.dlsym (libz3, "Z3_get_context_assignment")
    : _import Z3_context -> Z3_ast

  val Z3_get_error_msg =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_error_msg")
      : _import Z3_error_code -> char ptr)

end (* local *)
end

