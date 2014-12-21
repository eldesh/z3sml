
structure Z3_Stringconv =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context   = unit ptr
  type Z3_ast       = unit ptr
  type Z3_string    = string
  type Z3_pattern   = unit ptr
  type Z3_model     = unit ptr
  type Z3_func_decl = unit ptr
  type Z3_sort      = unit ptr
  type Z3_ast_print_mode = Z3_enum.Z3_ast_print_mode

  val Z3_set_ast_print_mode =
    Dyn.dlsym(libz3, "Z3_set_ast_print_mode")
    : _import (Z3_context, Z3_ast_print_mode) -> ()

  val Z3_ast_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_ast_to_string")
     : _import (Z3_context, Z3_ast) -> char ptr)

  val Z3_pattern_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_pattern_to_string")
     : _import (Z3_context, Z3_pattern) -> char ptr)

  val Z3_sort_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_sort_to_string")
     : _import (Z3_context, Z3_sort) -> char ptr)

  val Z3_func_decl_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_func_decl_to_string")
     : _import (Z3_context, Z3_func_decl) -> char ptr)

  val Z3_model_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_model_to_string")
     : _import (Z3_context, Z3_model) -> char ptr)

  val Z3_benchmark_to_smtlib_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_benchmark_to_smtlib_string")
     : _import (Z3_context, Z3_string, Z3_string
                , Z3_string, Z3_string
                , word, Z3_ast array, Z3_ast
                ) -> char ptr)

end (* local *)
end

