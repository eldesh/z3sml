
structure Z3_Parameter =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context      = unit ptr
  type Z3_params       = unit ptr
  type Z3_symbol       = unit ptr
  type Z3_param_descrs = unit ptr
  type Z3_bool         = int
  type Z3_string       = String.string
 
  val Z3_mk_params =
    Dyn.dlsym (libz3, "Z3_mk_params")
    : _import Z3_context -> Z3_params

  val Z3_params_inc_ref =
    Dyn.dlsym (libz3, "Z3_params_inc_ref")
    : _import (Z3_context, Z3_params) -> ()

  val Z3_params_dec_ref =
    Dyn.dlsym (libz3, "Z3_params_dec_ref")
    : _import (Z3_context, Z3_params) -> ()

  val Z3_params_set_bool =
    Dyn.dlsym (libz3, "Z3_params_set_bool")
    : _import (Z3_context, Z3_params, Z3_symbol, Z3_bool) -> ()

  val Z3_params_set_uint =
    Dyn.dlsym (libz3, "Z3_params_set_uint")
    : _import (Z3_context, Z3_params, Z3_symbol, Word32.word) -> ()

  val Z3_params_set_double =
    Dyn.dlsym (libz3, "Z3_params_set_double")
    : _import (Z3_context, Z3_params, Z3_symbol, Real.real) -> ()

  val Z3_params_set_symbol =
    Dyn.dlsym (libz3, "Z3_params_set_symbol")
    : _import (Z3_context, Z3_params, Z3_symbol, Z3_symbol) -> ()

  val Z3_params_to_string =
    Ptr.importString o
    ( Dyn.dlsym (libz3, "Z3_params_to_string")
      : _import (Z3_context, Z3_params) -> char ptr
      )

  val Z3_params_validate =
    Dyn.dlsym (libz3, "Z3_params_validate")
    : _import (Z3_context, Z3_params, Z3_param_descrs) -> ()

end (* local *)
end

