
structure Z3_Solver =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_solver  = unit ptr
  type Z3_symbol  = unit ptr
  type Z3_tactic  = unit ptr
  type Z3_params  = unit ptr
  type Z3_param_descrs = unit ptr
  type Z3_model   = unit ptr
  type Z3_stats   = unit ptr
  type Z3_ast     = unit ptr
  type Z3_ast_vector = unit ptr
  type Z3_string  = String.string
  type Z3_lbool   = Z3_enum.Z3_lbool

  val Z3_mk_solver =
    Dyn.dlsym(libz3, "Z3_mk_solver")
    : _import Z3_context -> Z3_solver
     
  val Z3_mk_simple_solver =
    Dyn.dlsym(libz3, "Z3_mk_simple_solver")
    : _import Z3_context -> Z3_solver
     
  val Z3_mk_solver_for_logic =
    Dyn.dlsym(libz3, "Z3_mk_solver_for_logic")
    : _import (Z3_context, Z3_symbol) -> Z3_solver
     
  val Z3_mk_solver_from_tactic =
    Dyn.dlsym(libz3, "Z3_mk_solver_from_tactic")
    : _import (Z3_context, Z3_tactic) -> Z3_solver
     
  val Z3_solver_get_help =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_solver_get_help")
    : _import (Z3_context, Z3_solver) -> char ptr)
     
  val Z3_solver_get_param_descrs =
    Dyn.dlsym(libz3, "Z3_solver_get_param_descrs")
    : _import (Z3_context, Z3_solver) -> Z3_param_descrs
     
  val Z3_solver_set_params =
    Dyn.dlsym(libz3, "Z3_solver_set_params")
    : _import (Z3_context, Z3_solver, Z3_params) -> ()
     
  val Z3_solver_inc_ref =
    Dyn.dlsym(libz3, "Z3_solver_inc_ref")
    : _import (Z3_context, Z3_solver) -> ()
     
  val Z3_solver_dec_ref =
    Dyn.dlsym(libz3, "Z3_solver_dec_ref")
    : _import (Z3_context, Z3_solver) -> ()
     
  val Z3_solver_push =
    Dyn.dlsym(libz3, "Z3_solver_push")
    : _import (Z3_context, Z3_solver) -> ()
     
  val Z3_solver_pop =
    Dyn.dlsym(libz3, "Z3_solver_pop")
    : _import (Z3_context, Z3_solver, word) -> ()
     
  val Z3_solver_reset =
    Dyn.dlsym(libz3, "Z3_solver_reset")
    : _import (Z3_context, Z3_solver) -> ()
     
  val Z3_solver_get_num_scopes =
    Dyn.dlsym(libz3, "Z3_solver_get_num_scopes")
    : _import (Z3_context, Z3_solver) -> word
     
  val Z3_solver_assert =
    Dyn.dlsym(libz3, "Z3_solver_assert")
    : _import (Z3_context, Z3_solver, Z3_ast) -> ()
     
  val Z3_solver_assert_and_track =
    Dyn.dlsym(libz3, "Z3_solver_assert_and_track")
    : _import (Z3_context, Z3_solver, Z3_ast, Z3_ast) -> ()
     
  val Z3_solver_get_assertions =
    Dyn.dlsym(libz3, "Z3_solver_get_assertions")
    : _import (Z3_context, Z3_solver) -> Z3_ast_vector
     
  val Z3_solver_check =
    Dyn.dlsym(libz3, "Z3_solver_check")
    : _import (Z3_context, Z3_solver) -> Z3_lbool
     
  fun Z3_solver_check_assumptions (c, s, assumptions) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_solver_check_assumptions"))
    ( c : Z3_context
    , s : Z3_solver
    , Vector.length assumptions : int
    , assumptions : Z3_ast vector) : Z3_lbool
     
  val Z3_solver_get_model =
    Dyn.dlsym(libz3, "Z3_solver_get_model")
    : _import (Z3_context, Z3_solver) -> Z3_model
     
  val Z3_solver_get_proof =
    Dyn.dlsym(libz3, "Z3_solver_get_proof")
    : _import (Z3_context, Z3_solver) -> Z3_ast
     
  val Z3_solver_get_unsat_core =
    Dyn.dlsym(libz3, "Z3_solver_get_unsat_core")
    : _import (Z3_context, Z3_solver) -> Z3_ast_vector
     
  val Z3_solver_get_reason_unknown =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_solver_get_reason_unknown")
    : _import (Z3_context, Z3_solver) -> char ptr)
     
  val Z3_solver_get_statistics =
    Dyn.dlsym(libz3, "Z3_solver_get_statistics")
    : _import (Z3_context, Z3_solver) -> Z3_stats
     
  val Z3_solver_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_solver_to_string")
    : _import (Z3_context, Z3_solver) -> char ptr)

end (* local *)
end


