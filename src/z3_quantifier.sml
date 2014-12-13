
structure Z3_Quantifier =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_pattern = unit ptr
  type Z3_sort    = unit ptr
  type Z3_ast     = unit ptr
  type Z3_app     = unit ptr
  type Z3_symbol  = unit ptr
  type Z3_bool    = int

  val Z3_mk_pattern =
    Dyn.dlsym(libz3, "Z3_mk_pattern")
    : _import (Z3_context, word, Z3_ast array) -> Z3_pattern

  val Z3_mk_bound =
    Dyn.dlsym(libz3, "Z3_mk_bound")
    : _import (Z3_context, word, Z3_sort) -> Z3_ast

  val Z3_mk_forall =
    Dyn.dlsym(libz3, "Z3_mk_forall")
    : _import (Z3_context, word, word, Z3_pattern, word, Z3_sort,
    Z3_symbol vector, Z3_ast) -> Z3_ast

  val Z3_mk_exists =
    Dyn.dlsym(libz3, "Z3_mk_exists")
    : _import (Z3_context, word, word, Z3_pattern, word, Z3_sort,
    Z3_symbol vector, Z3_ast) -> Z3_ast

  val Z3_mk_quantifier =
    Dyn.dlsym(libz3, "Z3_mk_quantifier")
    : _import (Z3_context, Z3_bool, word, word, Z3_pattern, word,
    Z3_sort, Z3_symbol vector, Z3_ast) -> Z3_ast

  val Z3_mk_quantifier_ex =
    Dyn.dlsym(libz3, "Z3_mk_quantifier_ex")
    : _import (Z3_context, Z3_bool, word
                , Z3_symbol, Z3_symbol, word
                , Z3_pattern, word, Z3_ast vector
                , word, Z3_sort, Z3_symbol vector, Z3_ast
                ) -> Z3_ast

  val Z3_mk_forall_const =
    Dyn.dlsym(libz3, "Z3_mk_forall_const")
    : _import (Z3_context, word, word, Z3_app, word, Z3_pattern, Z3_ast) -> Z3_ast

  val Z3_mk_exists_const =
    Dyn.dlsym(libz3, "Z3_mk_exists_const")
    : _import (Z3_context, word, word, Z3_app, word, Z3_pattern, Z3_ast) -> Z3_ast

  val Z3_mk_quantifier_const =
    Dyn.dlsym(libz3, "Z3_mk_quantifier_const")
    : _import (Z3_context, Z3_bool, word, word, Z3_app
                , word, Z3_pattern, Z3_ast
                ) -> Z3_ast

  val Z3_mk_quantifier_const_ex =
    Dyn.dlsym(libz3, "Z3_mk_quantifier_const_ex")
    : _import (Z3_context, Z3_bool, word, Z3_symbol
                , Z3_symbol, word, Z3_app, word
                , Z3_pattern, word, Z3_ast vector, Z3_ast
                ) -> Z3_ast

end (* local *)
end

