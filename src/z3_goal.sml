
structure Z3_Goal =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context   = unit ptr
  type Z3_goal      = unit ptr
  type Z3_ast       = unit ptr
  type Z3_bool      = int
  type Z3_goal_prec = Z3_enum.Z3_goal_prec
  type Z3_string    = String.string

  val Z3_mk_goal =
    Dyn.dlsym(libz3, "Z3_mk_goal")
    : _import (Z3_context, Z3_bool, Z3_bool, Z3_bool) -> Z3_goal
     
  val Z3_goal_inc_ref =
    Dyn.dlsym(libz3, "Z3_goal_inc_ref")
    : _import (Z3_context, Z3_goal) -> ()
     
  val Z3_goal_dec_ref =
    Dyn.dlsym(libz3, "Z3_goal_dec_ref")
    : _import (Z3_context, Z3_goal) -> ()
     
  val Z3_goal_precision =
    Dyn.dlsym(libz3, "Z3_goal_precision")
    : _import (Z3_context, Z3_goal) -> Z3_goal_prec
     
  val Z3_goal_assert =
    Dyn.dlsym(libz3, "Z3_goal_assert")
    : _import (Z3_context, Z3_goal, Z3_ast) -> ()
     
  val Z3_goal_inconsistent =
    Dyn.dlsym(libz3, "Z3_goal_inconsistent")
    : _import (Z3_context, Z3_goal) -> Z3_bool
     
  val Z3_goal_depth =
    Dyn.dlsym(libz3, "Z3_goal_depth")
    : _import (Z3_context, Z3_goal) -> word
     
  val Z3_goal_reset =
    Dyn.dlsym(libz3, "Z3_goal_reset")
    : _import (Z3_context, Z3_goal) -> ()
     
  val Z3_goal_size =
    Dyn.dlsym(libz3, "Z3_goal_size")
    : _import (Z3_context, Z3_goal) -> word
     
  val Z3_goal_formula =
    Dyn.dlsym(libz3, "Z3_goal_formula")
    : _import (Z3_context, Z3_goal, word) -> Z3_ast
     
  val Z3_goal_num_exprs =
    Dyn.dlsym(libz3, "Z3_goal_num_exprs")
    : _import (Z3_context, Z3_goal) -> word
     
  val Z3_goal_is_decided_sat =
    Dyn.dlsym(libz3, "Z3_goal_is_decided_sat")
    : _import (Z3_context, Z3_goal) -> Z3_bool
     
  val Z3_goal_is_decided_unsat =
    Dyn.dlsym(libz3, "Z3_goal_is_decided_unsat")
    : _import (Z3_context, Z3_goal) -> Z3_bool
     
  val Z3_goal_translate =
    Dyn.dlsym(libz3, "Z3_goal_translate")
    : _import (Z3_context, Z3_goal, Z3_context) -> Z3_goal
     
  val Z3_goal_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_goal_to_string")
    : _import (Z3_context, Z3_goal) -> char ptr)

end (* local *)
end

