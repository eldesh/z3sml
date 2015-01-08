
structure Z3_Interpolation =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_ast        = unit ptr
  type Z3_context    = unit ptr
  type Z3_string     = String.string
  type Z3_config     = unit ptr
  type Z3_params     = unit ptr
  type Z3_lbool      = Z3_enum.Z3_lbool
  type Z3_ast_vector = unit ptr
  type Z3_model      = unit ptr

  val Z3_mk_interpolant =
    Dyn.dlsym(libz3, "Z3_mk_interpolant")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_interpolation_context =
    Dyn.dlsym(libz3, "Z3_mk_interpolation_context")
    : _import Z3_config -> Z3_config

  val Z3_get_interpolant =
    Dyn.dlsym(libz3, "Z3_get_interpolant")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_params) -> Z3_ast_vector

  val Z3_compute_interpolant =
    Dyn.dlsym(libz3, "Z3_compute_interpolant")
    : _import (Z3_context, Z3_ast, Z3_params
             , Z3_ast_vector ref, Z3_model ref) -> Z3_lbool

  val Z3_interpolation_profile =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_interpolation_profile")
    : _import Z3_context -> char ptr)

  val Z3_read_interpolation_problem  =
    Dyn.dlsym(libz3, "Z3_read_interpolation_problem")
    : _import (Z3_context * word ref * Z3_ast ref ptr
               * word ref ptr * Z3_string
               * Z3_string ref * word ref * Z3_ast ref ptr) -> int

  fun Z3_check_interpolant (ctx, cnsts, parents, interps, error, theory) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_check_interpolant"))
    ( ctx : Z3_context
    , Array.length parents : int
    , cnsts : Z3_ast array
    , parents : word array
    , interps : Z3_ast array
    , error : Z3_string ref
    , Array.length theory : int
    , theory : Z3_ast array) : int
              
  fun Z3_write_interpolation_problem (ctx, cnsts, parents, filename, theory) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_write_interpolation_problem"))
    ( ctx : Z3_context
    , Array.length cnsts : int
    , cnsts : Z3_ast array
    , parents : word array
    , filename : Z3_string
    , Array.length theory : int
    , theory : Z3_ast array) : ()

end (* local *)
end

