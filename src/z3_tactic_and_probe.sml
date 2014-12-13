
structure Z3_Tactic_And_Probe =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_tactic  = unit ptr
  type Z3_probe   = unit ptr
  type Z3_goal    = unit ptr
  type Z3_apply_result = unit ptr
  type Z3_params  = unit ptr
  type Z3_model   = unit ptr
  type Z3_string  = String.string
  type Z3_param_descrs = unit ptr

  val Z3_mk_tactic =
    Dyn.dlsym(libz3, "Z3_mk_tactic")
    : _import (Z3_context, Z3_string) -> Z3_tactic
     
  val Z3_tactic_inc_ref =
    Dyn.dlsym(libz3, "Z3_tactic_inc_ref")
    : _import (Z3_context, Z3_tactic) -> ()
     
  val Z3_tactic_dec_ref =
    Dyn.dlsym(libz3, "Z3_tactic_dec_ref")
    : _import (Z3_context, Z3_tactic) -> ()
     
  val Z3_mk_probe =
    Dyn.dlsym(libz3, "Z3_mk_probe")
    : _import (Z3_context, Z3_string) -> Z3_probe
     
  val Z3_probe_inc_ref =
    Dyn.dlsym(libz3, "Z3_probe_inc_ref")
    : _import (Z3_context, Z3_probe) -> ()
     
  val Z3_probe_dec_ref =
    Dyn.dlsym(libz3, "Z3_probe_dec_ref")
    : _import (Z3_context, Z3_probe) -> ()
     
  val Z3_tactic_and_then =
    Dyn.dlsym(libz3, "Z3_tactic_and_then")
    : _import (Z3_context, Z3_tactic, Z3_tactic) -> Z3_tactic
     
  val Z3_tactic_or_else =
    Dyn.dlsym(libz3, "Z3_tactic_or_else")
    : _import (Z3_context, Z3_tactic, Z3_tactic) -> Z3_tactic
     
  val Z3_tactic_par_or =
    Dyn.dlsym(libz3, "Z3_tactic_par_or")
    : _import (Z3_context, word, Z3_tactic vector) -> Z3_tactic
     
  val Z3_tactic_par_and_then =
    Dyn.dlsym(libz3, "Z3_tactic_par_and_then")
    : _import (Z3_context, Z3_tactic, Z3_tactic) -> Z3_tactic
     
  val Z3_tactic_try_for =
    Dyn.dlsym(libz3, "Z3_tactic_try_for")
    : _import (Z3_context, Z3_tactic, word) -> Z3_tactic
     
  val Z3_tactic_when =
    Dyn.dlsym(libz3, "Z3_tactic_when")
    : _import (Z3_context, Z3_probe, Z3_tactic) -> Z3_tactic
     
  val Z3_tactic_cond =
    Dyn.dlsym(libz3, "Z3_tactic_cond")
    : _import (Z3_context, Z3_probe, Z3_tactic, Z3_tactic) -> Z3_tactic
     
  val Z3_tactic_repeat =
    Dyn.dlsym(libz3, "Z3_tactic_repeat")
    : _import (Z3_context, Z3_tactic, word) -> Z3_tactic
     
  val Z3_tactic_skip =
    Dyn.dlsym(libz3, "Z3_tactic_skip")
    : _import Z3_context -> Z3_tactic
     
  val Z3_tactic_fail =
    Dyn.dlsym(libz3, "Z3_tactic_fail")
    : _import Z3_context -> Z3_tactic
     
  val Z3_tactic_fail_if =
    Dyn.dlsym(libz3, "Z3_tactic_fail_if")
    : _import (Z3_context, Z3_probe) -> Z3_tactic
     
  val Z3_tactic_fail_if_not_decided =
    Dyn.dlsym(libz3, "Z3_tactic_fail_if_not_decided")
    : _import Z3_context -> Z3_tactic
     
  val Z3_tactic_using_params =
    Dyn.dlsym(libz3, "Z3_tactic_using_params")
    : _import (Z3_context, Z3_tactic, Z3_params) -> Z3_tactic
     
  val Z3_probe_const =
    Dyn.dlsym(libz3, "Z3_probe_const")
    : _import (Z3_context, real) -> Z3_probe
     
  val Z3_probe_lt =
    Dyn.dlsym(libz3, "Z3_probe_lt")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_gt =
    Dyn.dlsym(libz3, "Z3_probe_gt")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_le =
    Dyn.dlsym(libz3, "Z3_probe_le")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_ge =
    Dyn.dlsym(libz3, "Z3_probe_ge")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_eq =
    Dyn.dlsym(libz3, "Z3_probe_eq")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_and =
    Dyn.dlsym(libz3, "Z3_probe_and")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_or =
    Dyn.dlsym(libz3, "Z3_probe_or")
    : _import (Z3_context, Z3_probe, Z3_probe) -> Z3_probe
     
  val Z3_probe_not =
    Dyn.dlsym(libz3, "Z3_probe_not")
    : _import (Z3_context, Z3_probe) -> Z3_probe
     
  val Z3_get_num_tactics =
    Dyn.dlsym(libz3, "Z3_get_num_tactics")
    : _import Z3_context -> word
     
  val Z3_get_tactic_name =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_tactic_name")
      : _import (Z3_context, word) -> char ptr)
     
  val Z3_get_num_probes =
    Dyn.dlsym(libz3, "Z3_get_num_probes")
    : _import Z3_context -> word
     
  val Z3_get_probe_name =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_probe_name")
      : _import (Z3_context, word) -> char ptr)
     
  val Z3_tactic_get_help =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_tactic_get_help")
      : _import (Z3_context, Z3_tactic) -> char ptr)
     
  val Z3_tactic_get_param_descrs =
    Dyn.dlsym(libz3, "Z3_tactic_get_param_descrs")
    : _import (Z3_context, Z3_tactic) -> Z3_param_descrs
     
  val Z3_tactic_get_descr =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_tactic_get_descr")
      : _import (Z3_context, Z3_string) -> char ptr)
     
  val Z3_probe_get_descr =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_probe_get_descr")
      : _import (Z3_context, Z3_string) -> char ptr)
     
  val Z3_probe_apply =
    Dyn.dlsym(libz3, "Z3_probe_apply")
    : _import (Z3_context, Z3_probe, Z3_goal) -> real
     
  val Z3_tactic_apply =
    Dyn.dlsym(libz3, "Z3_tactic_apply")
    : _import (Z3_context, Z3_tactic, Z3_goal) -> Z3_apply_result
     
  val Z3_tactic_apply_ex =
    Dyn.dlsym(libz3, "Z3_tactic_apply_ex")
    : _import (Z3_context, Z3_tactic, Z3_goal, Z3_params) -> Z3_apply_result
     
  val Z3_apply_result_inc_ref =
    Dyn.dlsym(libz3, "Z3_apply_result_inc_ref")
    : _import (Z3_context, Z3_apply_result) -> ()
     
  val Z3_apply_result_dec_ref =
    Dyn.dlsym(libz3, "Z3_apply_result_dec_ref")
    : _import (Z3_context, Z3_apply_result) -> ()
     
  val Z3_apply_result_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_apply_result_to_string")
      : _import (Z3_context, Z3_apply_result) -> char ptr)
     
  val Z3_apply_result_get_num_subgoals =
    Dyn.dlsym(libz3, "Z3_apply_result_get_num_subgoals")
    : _import (Z3_context, Z3_apply_result) -> word
     
  val Z3_apply_result_get_subgoal =
    Dyn.dlsym(libz3, "Z3_apply_result_get_subgoal")
    : _import (Z3_context, Z3_apply_result, word) -> Z3_goal
     
  val Z3_apply_result_convert_model =
    Dyn.dlsym(libz3, "Z3_apply_result_convert_model")
    : _import (Z3_context, Z3_apply_result, word, Z3_model) -> Z3_model

end (* local *)
end
