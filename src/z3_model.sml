
structure Z3_Model =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context     = unit ptr
  type Z3_model       = unit ptr
  type Z3_ast         = unit ptr
  type Z3_func_decl   = unit ptr
  type Z3_func_interp = unit ptr
  type Z3_sort        = unit ptr
  type Z3_func_entry  = unit ptr
  type Z3_ast_vector  = unit ptr
  type Z3_bool        = Z3_bool.t

  val Z3_model_inc_ref =
    Dyn.dlsym(libz3, "Z3_model_inc_ref")
    : _import (Z3_context, Z3_model) -> ()

  val Z3_model_dec_ref =
    Dyn.dlsym(libz3, "Z3_model_dec_ref")
    : _import (Z3_context, Z3_model) -> ()

  fun Z3_model_eval (c, m, t, model_completion, v) =
    Z3_bool.fromInt
    (_ffiapply (Dyn.dlsym(libz3, "Z3_model_eval"))
      ( c : Z3_context
      , m : Z3_model
      , t : Z3_ast
      , Z3_bool.toInt model_completion : int
      , v : Z3_ast ref) : int)

  val Z3_model_get_const_interp =
    Dyn.dlsym(libz3, "Z3_model_get_const_interp")
    : _import (Z3_context, Z3_model, Z3_func_decl) -> Z3_ast

  val Z3_model_get_func_interp =
    Dyn.dlsym(libz3, "Z3_model_get_func_interp")
    : _import (Z3_context, Z3_model, Z3_func_decl) -> Z3_func_interp

  val Z3_model_get_num_consts =
    Dyn.dlsym(libz3, "Z3_model_get_num_consts")
    : _import (Z3_context, Z3_model) -> word

  val Z3_model_get_const_decl =
    Dyn.dlsym(libz3, "Z3_model_get_const_decl")
    : _import (Z3_context, Z3_model, word) -> Z3_func_decl

  val Z3_model_get_num_funcs =
    Dyn.dlsym(libz3, "Z3_model_get_num_funcs")
    : _import (Z3_context, Z3_model) -> word

  val Z3_model_get_func_decl =
    Dyn.dlsym(libz3, "Z3_model_get_func_decl")
    : _import (Z3_context, Z3_model, word) -> Z3_func_decl

  val Z3_model_get_num_sorts =
    Dyn.dlsym(libz3, "Z3_model_get_num_sorts")
    : _import (Z3_context, Z3_model) -> word

  val Z3_model_get_sort =
    Dyn.dlsym(libz3, "Z3_model_get_sort")
    : _import (Z3_context, Z3_model, word) -> Z3_sort

  val Z3_model_get_sort_universe =
    Dyn.dlsym(libz3, "Z3_model_get_sort_universe")
    : _import (Z3_context, Z3_model, Z3_sort) -> Z3_ast_vector

  val Z3_is_as_array =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_as_array")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_get_as_array_func_decl =
    Dyn.dlsym(libz3, "Z3_get_as_array_func_decl")
    : _import (Z3_context, Z3_ast) -> Z3_func_decl

  val Z3_func_interp_inc_ref =
    Dyn.dlsym(libz3, "Z3_func_interp_inc_ref")
    : _import (Z3_context, Z3_func_interp) -> ()

  val Z3_func_interp_dec_ref =
    Dyn.dlsym(libz3, "Z3_func_interp_dec_ref")
    : _import (Z3_context, Z3_func_interp) -> ()

  val Z3_func_interp_get_num_entries =
    Dyn.dlsym(libz3, "Z3_func_interp_get_num_entries")
    : _import (Z3_context, Z3_func_interp) -> word

  val Z3_func_interp_get_entry =
    Dyn.dlsym(libz3, "Z3_func_interp_get_entry")
    : _import (Z3_context, Z3_func_interp, word) -> Z3_func_entry

  val Z3_func_interp_get_else =
    Dyn.dlsym(libz3, "Z3_func_interp_get_else")
    : _import (Z3_context, Z3_func_interp) -> Z3_ast

  val Z3_func_interp_get_arity =
    Dyn.dlsym(libz3, "Z3_func_interp_get_arity")
    : _import (Z3_context, Z3_func_interp) -> word

  val Z3_func_entry_inc_ref =
    Dyn.dlsym(libz3, "Z3_func_entry_inc_ref")
    : _import (Z3_context, Z3_func_entry) -> ()

  val Z3_func_entry_dec_ref =
    Dyn.dlsym(libz3, "Z3_func_entry_dec_ref")
    : _import (Z3_context, Z3_func_entry) -> ()

  val Z3_func_entry_get_value =
    Dyn.dlsym(libz3, "Z3_func_entry_get_value")
    : _import (Z3_context, Z3_func_entry) -> Z3_ast

  val Z3_func_entry_get_num_args =
    Dyn.dlsym(libz3, "Z3_func_entry_get_num_args")
    : _import (Z3_context, Z3_func_entry) -> word

  val Z3_func_entry_get_arg =
    Dyn.dlsym(libz3, "Z3_func_entry_get_arg")
    : _import (Z3_context, Z3_func_entry, word) -> Z3_ast

end (* local *)
end

