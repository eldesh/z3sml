
structure Z3_Global =
struct
local
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_bool   = Z3_bool.t
  type Z3_string = String.string

  val Z3_global_param_set =
    Dyn.dlsym (libz3, "Z3_global_param_set")
    : _import (Z3_string, Z3_string) -> ()

  val Z3_global_param_reset_all =
    Dyn.dlsym (libz3, "Z3_global_param_reset_all")
    : _import () -> ()

  val Z3_global_param_get =
    Z3_bool.fromInt o
      (Dyn.dlsym (libz3, "Z3_global_param_get")
       : _import (Z3_string, Z3_string ref) -> int)

end (* local *)
end

