
structure Z3_Deprecated =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_model   = unit ptr
  type Z3_ast     = unit ptr
  type Z3_lbool   = Z3_enum.Z3_lbool

  val Z3_check_and_get_model =
    Dyn.dlsym (libz3, "Z3_check_and_get_model")
    : _import (Z3_context, Z3_model ref) -> Z3_lbool

  val Z3_check =
    Dyn.dlsym (libz3, "Z3_check")
    : _import Z3_context -> Z3_lbool

  val Z3_del_model =
    Dyn.dlsym (libz3, "Z3_del_model")
    : _import (Z3_context, Z3_model) -> ()

  val Z3_assert_cnstr =
    Dyn.dlsym (libz3, "Z3_assert_cnstr")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_context_to_string =
    Ptr.importString o
    (Dyn.dlsym (libz3, "Z3_context_to_string")
    : _import Z3_context -> char ptr)

end (* local *)
end

