
structure Z3_Config =
struct
local
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_config = unit ptr
  type Z3_string = String.string

  val Z3_mk_config =
    Dyn.dlsym (libz3, "Z3_mk_config")
    : _import () -> Z3_config

  val Z3_del_config =
    Dyn.dlsym (libz3, "Z3_del_config")
    : _import Z3_config -> ()

  val Z3_set_param_value =
    Dyn.dlsym (libz3, "Z3_set_param_value")
    : _import (Z3_config, Z3_string, Z3_string) -> ()
end (* local *)
end

