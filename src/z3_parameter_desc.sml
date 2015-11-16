
structure Z3_ParameterDesc =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context      = unit ptr
  type Z3_param_descrs = unit ptr
  type Z3_symbol       = unit ptr
  type Z3_string       = String.string
 
  val Z3_param_descrs_inc_ref =
    Dyn.dlsym (libz3, "Z3_param_descrs_inc_ref")
    : _import (Z3_context, Z3_param_descrs) -> ()

  val Z3_param_descrs_dec_ref =
    Dyn.dlsym (libz3, "Z3_param_descrs_dec_ref")
    : _import (Z3_context, Z3_param_descrs) -> ()

  val Z3_param_descrs_get_kind =
    Z3_param_kind.fromInt o (
    Dyn.dlsym (libz3, "Z3_param_descrs_get_kind")
    : _import (Z3_context, Z3_param_descrs, Z3_symbol) -> int)

  val Z3_param_descrs_size =
    Dyn.dlsym (libz3, "Z3_param_descrs_get_kind")
    : _import (Z3_context, Z3_param_descrs) -> Word32.word

  val Z3_param_descrs_get_name =
    Dyn.dlsym (libz3, "Z3_param_descrs_get_name")
    : _import (Z3_context, Z3_param_descrs, word) -> Z3_symbol

  val Z3_param_descrs_to_string =
    Ptr.importString o
    ( Dyn.dlsym (libz3, "Z3_param_descrs_to_string")
      : _import (Z3_context, Z3_param_descrs) -> char ptr
      )

end (* local *)
end

