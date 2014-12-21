
structure Z3_Error =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_error_code = Z3_enum.Z3_error_code
  type Z3_error_handler = Z3_context * Z3_error_code -> unit
  type Z3_string = string

  val Z3_get_error_code =
    Dyn.dlsym(libz3, "Z3_get_error_code")
    : _import Z3_context -> Z3_error_code

  val Z3_set_error_handler =
    Dyn.dlsym(libz3, "Z3_set_error_handler")
    : _import (Z3_context, (Z3_context, Z3_error_code)->()) -> ()

  val Z3_set_error =
    Dyn.dlsym(libz3, "Z3_set_error")
    : _import (Z3_context, Z3_error_code) -> ()

  (**
   * BEGIN_MLAPI_EXCLUDE Z3_string
   *)
  val Z3_get_error_msg_ex =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_error_msg_ex")
      : _import (Z3_context, Z3_error_code) -> char ptr)

end (* local *)
end

