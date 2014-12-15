
structure Z3_RealClosedField =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_rcf_num = unit ptr
  type Z3_string  = String.string
  type Z3_bool    = int

  val Z3_rcf_del =
    Dyn.dlsym(libz3, "Z3_rcf_del")
    : _import (Z3_context, Z3_rcf_num) -> ()

  val Z3_rcf_mk_rational =
    Dyn.dlsym(libz3, "Z3_rcf_mk_rational")
    : _import (Z3_context, Z3_string) -> Z3_rcf_num

  val Z3_rcf_mk_small_int =
    Dyn.dlsym(libz3, "Z3_rcf_mk_small_int")
    : _import (Z3_context, int) -> Z3_rcf_num

  val Z3_rcf_mk_pi =
    Dyn.dlsym(libz3, "Z3_rcf_mk_pi")
    : _import Z3_context -> Z3_rcf_num

  val Z3_rcf_mk_e =
    Dyn.dlsym(libz3, "Z3_rcf_mk_e")
    : _import Z3_context -> Z3_rcf_num

  val Z3_rcf_mk_infinitesimal =
    Dyn.dlsym(libz3, "Z3_rcf_mk_infinitesimal")
    : _import Z3_context -> Z3_rcf_num

  val Z3_rcf_mk_roots =
    Dyn.dlsym(libz3, "Z3_rcf_mk_roots")
    : _import (Z3_context, word, Z3_rcf_num vector, Z3_rcf_num array) -> word

  val Z3_rcf_add =
    Dyn.dlsym(libz3, "Z3_rcf_add")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_sub =
    Dyn.dlsym(libz3, "Z3_rcf_sub")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_mul =
    Dyn.dlsym(libz3, "Z3_rcf_mul")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_div =
    Dyn.dlsym(libz3, "Z3_rcf_div")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_neg =
    Dyn.dlsym(libz3, "Z3_rcf_neg")
    : _import (Z3_context, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_inv =
    Dyn.dlsym(libz3, "Z3_rcf_inv")
    : _import (Z3_context, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_power =
    Dyn.dlsym(libz3, "Z3_rcf_power")
    : _import (Z3_context, Z3_rcf_num, word) -> Z3_rcf_num

  val Z3_rcf_lt =
    Dyn.dlsym(libz3, "Z3_rcf_lt")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_gt =
    Dyn.dlsym(libz3, "Z3_rcf_gt")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_le =
    Dyn.dlsym(libz3, "Z3_rcf_le")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_ge =
    Dyn.dlsym(libz3, "Z3_rcf_ge")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_eq =
    Dyn.dlsym(libz3, "Z3_rcf_eq")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_neq =
    Dyn.dlsym(libz3, "Z3_rcf_neq")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num) -> Z3_rcf_num

  val Z3_rcf_num_to_string =
    Pointer.importString o
    (Dyn.dlsym(libz3, "Z3_rcf_num_to_string")
    : _import (Z3_context, Z3_rcf_num, Z3_bool, Z3_bool) -> char ptr)

  val Z3_rcf_num_to_decimal_string =
    Pointer.importString o
    (Dyn.dlsym(libz3, "Z3_rcf_num_to_decimal_string")
    : _import (Z3_context, Z3_rcf_num, word) -> char ptr)

  val Z3_rcf_get_numerator_denominator =
    Dyn.dlsym(libz3, "Z3_rcf_get_numerator_denominator")
    : _import (Z3_context, Z3_rcf_num, Z3_rcf_num ref, Z3_rcf_num ref) -> ()

end (* local *)
end

