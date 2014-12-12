
structure Z3_Global =
struct
local
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_bool = int
  type Z3_string = String.string

  val Z3_global_param_set =
    Dyn.dlsym (libz3, "Z3_global_param_set")
    : _import (Z3_string, Z3_string) -> ()

  val Z3_global_param_reset_all =
    Dyn.dlsym (libz3, "Z3_global_param_reset_all")
    : _import () -> ()

  val Z3_global_param_get =
    Dyn.dlsym (libz3, "Z3_global_param_get")
    : _import (Z3_string, Z3_string ref) -> Z3_bool

end (* local *)
end

