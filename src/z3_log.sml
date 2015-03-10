
structure Z3_Log =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_string = string
  type Z3_bool   = Z3_bool.t

  val Z3_open_log =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_open_log")
       : _import Z3_string -> int)

  val Z3_append_log =
    Dyn.dlsym(libz3, "Z3_append_log")
    : _import Z3_string -> ()

  val Z3_close_log =
    Dyn.dlsym(libz3, "Z3_close_log")
    : _import () -> ()

  fun Z3_toggle_warning_messages enabled =
    _ffiapply (Dyn.dlsym(libz3, "Z3_toggle_warning_messages"))
    (Z3_bool.toInt enabled : int) : ()

end (* local *)
end

