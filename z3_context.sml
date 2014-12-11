
structure Z3_Context =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_config  = unit ptr
  type Z3_context = unit ptr
  type Z3_ast     = unit ptr
  type Z3_string  = String.string
  type Z3_bool    = int

  val Z3_mk_context =
    Dyn.dlsym (libz3, "Z3_mk_context")
    : _import Z3_config -> Z3_context

  val Z3_mk_context_rc =
    Dyn.dlsym (libz3, "Z3_mk_context_rc")
    : _import Z3_config -> Z3_context

  val Z3_del_context =
    Dyn.dlsym (libz3, "Z3_del_context")
    : _import Z3_context -> ()

  val Z3_inc_ref =
    Dyn.dlsym (libz3, "Z3_inc_ref")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_dec_ref =
    Dyn.dlsym (libz3, "Z3_dec_ref")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_update_param_value =
    Dyn.dlsym (libz3, "Z3_update_param_value")
    : _import (Z3_context, Z3_string, Z3_string) -> ()

  val Z3_interrupt =
    Dyn.dlsym (libz3, "Z3_interrupt")
    : _import Z3_context -> ()

end (* local *)
end

