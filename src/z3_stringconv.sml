
structure Z3_Stringconv =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
  open Z3_enum
in
  type Z3_context   = unit ptr
  type Z3_ast       = unit ptr
  type Z3_string    = string
  type Z3_pattern   = unit ptr
  type Z3_model     = unit ptr
  type Z3_func_decl = unit ptr
  type Z3_sort      = unit ptr

  fun Z3_set_ast_print_mode (c, mode) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_set_ast_print_mode"))
    ( c : Z3_context
    , Z3_ast_print_mode.toInt mode : int) : ()

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

  fun Z3_benchmark_to_smtlib_string (c, name, logic, status
                                    , attributes, assumptions, formula) =
    Ptr.importString (
      _ffiapply (Dyn.dlsym(libz3, "Z3_benchmark_to_smtlib_string"))
      ( c : Z3_context
      , name : Z3_string
      , logic : Z3_string
      , status : Z3_string
      , attributes : Z3_string
      , Vector.length assumptions : int
      , assumptions : Z3_ast vector
      , formula : Z3_ast) : char ptr)

end (* local *)
end

