
structure Z3_Log =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_string = string
  type Z3_bool   = int

  val Z3_open_log =
    Dyn.dlsym(libz3, "Z3_open_log")
    : _import Z3_string -> Z3_bool

  val Z3_append_log =
    Dyn.dlsym(libz3, "Z3_append_log")
    : _import Z3_string -> ()

  val Z3_close_log =
    Dyn.dlsym(libz3, "Z3_close_log")
    : _import () -> ()

  val Z3_toggle_warning_messages =
    Dyn.dlsym(libz3, "Z3_toggle_warning_messages")
    : _import Z3_bool -> ()

end (* local *)
end

