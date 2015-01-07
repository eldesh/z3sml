
structure Z3_Parser =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_symbol    = unit ptr
  type Z3_ast       = unit ptr
  type Z3_context   = unit ptr
  type Z3_sort      = unit ptr
  type Z3_func_decl = unit ptr
  type Z3_string    = String.string

  fun Z3_parse_smtlib2_string (c, str, sort_names, sorts, decl_names, decls) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_parse_smtlib2_string"))
    ( c : Z3_context
    , str : Z3_string
    , Vector.length sort_names : int, sort_names : Z3_symbol vector
    , sorts : Z3_sort vector
    , Vector.length decl_names : int, decl_names : Z3_symbol vector
    , decls : Z3_func_decl vector
    ) : Z3_ast

  fun Z3_parse_smtlib2_file (c, file_name, sort_names, sorts, decl_names, decls) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_parse_smtlib2_file"))
    ( c : Z3_context
    , file_name : Z3_string
    , Vector.length sort_names : int, sort_names : Z3_symbol vector
    , sorts : Z3_sort vector
    , Vector.length decl_names : int, decl_names : Z3_symbol vector
    , decls : Z3_func_decl vector
    ) : Z3_ast

  fun Z3_parse_smtlib_string (c, str, sort_names, sorts, decl_names, decls) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_parse_smtlib_string"))
    ( c : Z3_context
    , str : Z3_string
    , Vector.length sort_names : int, sort_names : Z3_symbol vector
    , sorts : Z3_sort vector
    , Vector.length decl_names : int, decl_names : Z3_symbol vector
    , decls : Z3_func_decl vector
    ) : ()

  fun Z3_parse_smtlib_file (c, file_name, sort_names, sorts, decl_names, decls) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_parse_smtlib_file"))
    ( c : Z3_context
    , file_name : Z3_string
    , Vector.length sort_names : int, sort_names : Z3_symbol vector
    , sorts : Z3_sort vector
    , Vector.length decl_names : int, decl_names : Z3_symbol vector
    , decls : Z3_func_decl vector
    ) : ()

  val Z3_get_smtlib_num_formulas =
    Dyn.dlsym(libz3, "Z3_get_smtlib_num_formulas")
    : _import Z3_context -> word

  val Z3_get_smtlib_formula =
    Dyn.dlsym(libz3, "Z3_get_smtlib_formula")
    : _import (Z3_context, word) -> Z3_ast

  val Z3_get_smtlib_num_assumptions =
    Dyn.dlsym(libz3, "Z3_get_smtlib_num_assumptions")
    : _import Z3_context -> word

  val Z3_get_smtlib_assumption =
    Dyn.dlsym(libz3, "Z3_get_smtlib_assumption")
    : _import (Z3_context, word) -> Z3_ast

  val Z3_get_smtlib_num_decls =
    Dyn.dlsym(libz3, "Z3_get_smtlib_num_decls")
    : _import Z3_context -> word

  val Z3_get_smtlib_decl =
    Dyn.dlsym(libz3, "Z3_get_smtlib_decl")
    : _import (Z3_context, word) -> Z3_func_decl

  val Z3_get_smtlib_num_sorts =
    Dyn.dlsym(libz3, "Z3_get_smtlib_num_sorts")
    : _import Z3_context -> word

  val Z3_get_smtlib_sort =
    Dyn.dlsym(libz3, "Z3_get_smtlib_sort")
    : _import (Z3_context, word) -> Z3_sort

  (**
   * BEGIN_MLAPI_EXCLUDE Z3_string
   *)
   val Z3_get_smtlib_error =
     Ptr.importString o
     (Dyn.dlsym(libz3, "Z3_get_smtlib_error")
      : _import Z3_context -> char ptr)

end (* local *)
end


