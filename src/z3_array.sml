
structure Z3_Array =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context   = unit ptr
  type Z3_ast       = unit ptr
  type Z3_sort      = unit ptr
  type Z3_func_decl = unit ptr
 
  val Z3_mk_select =
    Dyn.dlsym(libz3, "Z3_mk_select")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_store =
    Dyn.dlsym(libz3, "Z3_mk_store")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_const_array =
    Dyn.dlsym(libz3, "Z3_mk_const_array")
    : _import (Z3_context, Z3_sort, Z3_ast) -> Z3_ast

  val Z3_mk_map =
    Dyn.dlsym(libz3, "Z3_mk_map")
    : _import (Z3_context, Z3_func_decl, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_array_default =
    Dyn.dlsym(libz3, "Z3_mk_array_default")
    : _import (Z3_context, Z3_ast array) -> Z3_ast

end (* local *)
end

