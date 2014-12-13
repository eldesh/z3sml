
(**
 * Algebraic Numbers API
 *)
structure Z3_Algebraic =
struct
local
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_ast = unit ptr
  type Z3_bool = int
  type Z3_ast_vector = unit ptr

  val Z3_algebraic_is_value =
    Dyn.dlsym(libz3, "Z3_algebraic_is_value")
    : _import (Z3_context, Z3_ast) -> Z3_bool

  val Z3_algebraic_is_pos =
    Dyn.dlsym(libz3, "Z3_algebraic_is_pos")
    : _import (Z3_context, Z3_ast) -> Z3_bool

  val Z3_algebraic_is_neg =
    Dyn.dlsym(libz3, "Z3_algebraic_is_neg")
    : _import (Z3_context, Z3_ast) -> Z3_bool

  val Z3_algebraic_is_zero =
    Dyn.dlsym(libz3, "Z3_algebraic_is_zero")
    : _import (Z3_context, Z3_ast) -> Z3_bool

  val Z3_algebraic_sign =
    Dyn.dlsym(libz3, "Z3_algebraic_sign")
    : _import (Z3_context, Z3_ast) -> int

  val Z3_algebraic_add =
    Dyn.dlsym(libz3, "Z3_algebraic_add")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_algebraic_sub =
    Dyn.dlsym(libz3, "Z3_algebraic_sub")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_algebraic_mul =
    Dyn.dlsym(libz3, "Z3_algebraic_mul")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_algebraic_div =
    Dyn.dlsym(libz3, "Z3_algebraic_div")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_algebraic_root =
    Dyn.dlsym(libz3, "Z3_algebraic_root")
    : _import (Z3_context, Z3_ast, word) -> Z3_ast

  val Z3_algebraic_power =
    Dyn.dlsym(libz3, "Z3_algebraic_power")
    : _import (Z3_context, Z3_ast, word) -> Z3_ast

  val Z3_algebraic_lt =
    Dyn.dlsym(libz3, "Z3_algebraic_lt")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_gt =
    Dyn.dlsym(libz3, "Z3_algebraic_gt")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_le =
    Dyn.dlsym(libz3, "Z3_algebraic_le")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_ge =
    Dyn.dlsym(libz3, "Z3_algebraic_ge")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_eq =
    Dyn.dlsym(libz3, "Z3_algebraic_eq")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_neq =
    Dyn.dlsym(libz3, "Z3_algebraic_neq")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_bool

  val Z3_algebraic_roots =
    Dyn.dlsym(libz3, "Z3_algebraic_roots")
    : _import (Z3_context, Z3_ast, word, Z3_ast array) -> Z3_ast_vector

  val Z3_algebraic_eval =
    Dyn.dlsym(libz3, "Z3_algebraic_eval")
    : _import (Z3_context, Z3_ast, word, Z3_ast array) -> int

end (* local *)
end

