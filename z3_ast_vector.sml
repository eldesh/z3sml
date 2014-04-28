

structure Z3_Ast_Vector =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context    = unit ptr
  type Z3_ast        = unit ptr
  type Z3_ast_vector = unit ptr
  type Z3_string     = String.string

  val Z3_mk_ast_vector =
    Dyn.dlsym(libz3, "Z3_mk_ast_vector")
    : _import Z3_context -> Z3_ast_vector

  val Z3_ast_vector_inc_ref =
    Dyn.dlsym(libz3, "Z3_ast_vector_inc_ref")
    : _import (Z3_context, Z3_ast_vector) -> ()

  val Z3_ast_vector_dec_ref =
    Dyn.dlsym(libz3, "Z3_ast_vector_dec_ref")
    : _import (Z3_context, Z3_ast_vector) -> ()

  val Z3_ast_vector_size =
    Dyn.dlsym(libz3, "Z3_ast_vector_size")
    : _import (Z3_context, Z3_ast_vector) -> word

  val Z3_ast_vector_get =
    Dyn.dlsym(libz3, "Z3_ast_vector_get")
    : _import (Z3_context, Z3_ast_vector, word) -> Z3_ast

  val Z3_ast_vector_set =
    Dyn.dlsym(libz3, "Z3_ast_vector_set")
    : _import (Z3_context, Z3_ast_vector, word, Z3_ast) -> ()

  val Z3_ast_vector_resize =
    Dyn.dlsym(libz3, "Z3_ast_vector_resize")
    : _import (Z3_context, Z3_ast_vector, word) -> ()

  val Z3_ast_vector_push =
    Dyn.dlsym(libz3, "Z3_ast_vector_push")
    : _import (Z3_context, Z3_ast_vector, Z3_ast) -> ()

  val Z3_ast_vector_translate =
    Dyn.dlsym(libz3, "Z3_ast_vector_translate")
    : _import (Z3_context, Z3_ast_vector, Z3_context) -> Z3_ast_vector

  val Z3_ast_vector_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_ast_vector_to_string")
      : _import (Z3_context, Z3_ast_vector) -> char ptr)

end (* local *)
end

