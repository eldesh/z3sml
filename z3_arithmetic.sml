
structure Z3_Arithmetic =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context = unit ptr
  type Z3_ast     = unit ptr

  val Z3_mk_add =
    Dyn.dlsym(libz3, "Z3_mk_add") 
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_mul =
    Dyn.dlsym(libz3, "Z3_mk_mul") 
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_sub =
    Dyn.dlsym(libz3, "Z3_mk_sub") 
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_unary_minus =
    Dyn.dlsym(libz3, "Z3_mk_unary_minus") 
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_div =
    Dyn.dlsym(libz3, "Z3_mk_div") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_mod =
    Dyn.dlsym(libz3, "Z3_mk_mod") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_rem =
    Dyn.dlsym(libz3, "Z3_mk_rem") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_power =
    Dyn.dlsym(libz3, "Z3_mk_power") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_lt =
    Dyn.dlsym(libz3, "Z3_mk_lt") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_le =
    Dyn.dlsym(libz3, "Z3_mk_le") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_gt =
    Dyn.dlsym(libz3, "Z3_mk_gt") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_ge =
    Dyn.dlsym(libz3, "Z3_mk_ge") 
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_int2real =
    Dyn.dlsym(libz3, "Z3_mk_int2real") 
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_real2int =
    Dyn.dlsym(libz3, "Z3_mk_real2int") 
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_is_int =
    Dyn.dlsym(libz3, "Z3_mk_is_int") 
    : _import (Z3_context, Z3_ast) -> Z3_ast

end (* local *)
end

