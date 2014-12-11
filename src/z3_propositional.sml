
structure Z3_Propositional =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context = unit ptr
  type Z3_ast     = unit ptr

  val Z3_mk_true =
    Dyn.dlsym(libz3, "Z3_mk_true")
    : _import Z3_context -> Z3_ast

  val Z3_mk_false =
    Dyn.dlsym(libz3, "Z3_mk_false")
    : _import Z3_context -> Z3_ast

  val Z3_mk_eq =
    Dyn.dlsym(libz3, "Z3_mk_eq")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_distinct =
    Dyn.dlsym(libz3, "Z3_mk_distinct")
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_not =
    Dyn.dlsym(libz3, "Z3_mk_not") 
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_ite =
    Dyn.dlsym(libz3, "Z3_mk_ite") 
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_iff =
    Dyn.dlsym(libz3, "Z3_mk_iff") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_implies =
    Dyn.dlsym(libz3, "Z3_mk_implies") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_xor =
    Dyn.dlsym(libz3, "Z3_mk_xor") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_and =
    Dyn.dlsym(libz3, "Z3_mk_and") 
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_or =
    Dyn.dlsym(libz3, "Z3_mk_or") 
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

end (* local *)
end

