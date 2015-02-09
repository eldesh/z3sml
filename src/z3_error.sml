
structure Z3_Error =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_error_handler = Z3_context * Z3_enum.Z3_error_code.t -> unit
  type Z3_string = string

  val Z3_get_error_code =
    Z3_enum.Z3_error_code.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_error_code")
    : _import Z3_context -> int)

  val Z3_set_error_handler_func =
    Dyn.dlsym(libz3, "Z3_set_error_handler")
    : _import (Z3_context, (Z3_context, int)->()) -> ()

  (* specialized to the NULL pointer *)
  fun Z3_set_error_handler_null c =
    _ffiapply (Dyn.dlsym(libz3, "Z3_set_error_handler"))
    (c : Z3_context, Ptr.NULL() : unit ptr) : ()

  fun Z3_set_error_handler (ctx, NONE  ) =
        Z3_set_error_handler_null ctx
    | Z3_set_error_handler (ctx, SOME f) =
        Z3_set_error_handler_func (ctx, fn(c,e)=> f(c, Z3_enum.Z3_error_code.fromInt e))

  fun Z3_set_error (c, e) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_set_error"))
    ( c : Z3_context
    , Z3_enum.Z3_error_code.toInt e : int) : ()

  (**
   * BEGIN_MLAPI_EXCLUDE Z3_string
   *)
  fun Z3_get_error_msg_ex (c, err) =
    Ptr.importString (
      _ffiapply (Dyn.dlsym(libz3, "Z3_get_error_msg_ex"))
      ( c : Z3_context
      , Z3_enum.Z3_error_code.toInt err : int) : char ptr)

end (* local *)
end

