
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
  type Z3_bool      = Z3_bool.t
  type Z3_string    = String.string

  fun Z3_mk_goal (c, models, unsat_cores, proofs) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_goal"))
    ( c : Z3_context
    , Z3_bool.toInt models      : int
    , Z3_bool.toInt unsat_cores : int
    , Z3_bool.toInt proofs      : int) : Z3_goal
     
  val Z3_goal_inc_ref =
    Dyn.dlsym(libz3, "Z3_goal_inc_ref")
    : _import (Z3_context, Z3_goal) -> ()
     
  val Z3_goal_dec_ref =
    Dyn.dlsym(libz3, "Z3_goal_dec_ref")
    : _import (Z3_context, Z3_goal) -> ()
     
  val Z3_goal_precision =
    Z3_goal_prec.fromInt o (
    Dyn.dlsym(libz3, "Z3_goal_precision")
    : _import (Z3_context, Z3_goal) -> int)
     
  val Z3_goal_assert =
    Dyn.dlsym(libz3, "Z3_goal_assert")
    : _import (Z3_context, Z3_goal, Z3_ast) -> ()
     
  val Z3_goal_inconsistent =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_goal_inconsistent")
       : _import (Z3_context, Z3_goal) -> int)
     
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
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_goal_is_decided_sat")
       : _import (Z3_context, Z3_goal) -> int)
     
  val Z3_goal_is_decided_unsat =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_goal_is_decided_unsat")
       : _import (Z3_context, Z3_goal) -> int)
     
  val Z3_goal_translate =
    Dyn.dlsym(libz3, "Z3_goal_translate")
    : _import (Z3_context, Z3_goal, Z3_context) -> Z3_goal
     
  val Z3_goal_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_goal_to_string")
    : _import (Z3_context, Z3_goal) -> char ptr)

end (* local *)
end

