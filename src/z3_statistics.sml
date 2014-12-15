
structure Z3_Statistics =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_stats   = unit ptr
  type Z3_string  = String.string
  type Z3_bool    = int

  val Z3_stats_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_stats_to_string")
    : _import (Z3_context, Z3_stats) -> char ptr)

  val Z3_stats_inc_ref =
    Dyn.dlsym(libz3, "Z3_stats_inc_ref")
    : _import (Z3_context, Z3_stats) -> ()

  val Z3_stats_dec_ref =
    Dyn.dlsym(libz3, "Z3_stats_dec_ref")
    : _import (Z3_context, Z3_stats) -> ()

  val Z3_stats_size =
    Dyn.dlsym(libz3, "Z3_stats_size")
    : _import (Z3_context, Z3_stats) -> word

  val Z3_stats_get_key =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_stats_get_key")
    : _import (Z3_context, Z3_stats, word) -> char ptr)

  val Z3_stats_is_uint =
    Dyn.dlsym(libz3, "Z3_stats_is_uint")
    : _import (Z3_context, Z3_stats, word) -> Z3_bool

  val Z3_stats_is_double =
    Dyn.dlsym(libz3, "Z3_stats_is_double")
    : _import (Z3_context, Z3_stats, word) -> Z3_bool

  val Z3_stats_get_uint_value =
    Dyn.dlsym(libz3, "Z3_stats_get_uint_value")
    : _import (Z3_context, Z3_stats, word) -> word

  val Z3_stats_get_double_value =
    Dyn.dlsym(libz3, "Z3_stats_get_double_value")
    : _import (Z3_context, Z3_stats, word) -> real

end (* local *)
end

