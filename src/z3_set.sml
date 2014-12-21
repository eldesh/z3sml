
structure Z3_Set =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_sort    = unit ptr
  type Z3_ast     = unit ptr

  val Z3_mk_set_sort =
    Dyn.dlsym(libz3, "Z3_mk_set_sort")
    : _import (Z3_context, Z3_sort) -> Z3_sort

  val Z3_mk_empty_set =
    Dyn.dlsym(libz3, "Z3_mk_empty_set")
    : _import (Z3_context, Z3_sort) -> Z3_ast

  val Z3_mk_full_set =
    Dyn.dlsym(libz3, "Z3_mk_full_set")
    : _import (Z3_context, Z3_sort) -> Z3_ast

  val Z3_mk_set_add =
    Dyn.dlsym(libz3, "Z3_mk_set_add")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_set_del =
    Dyn.dlsym(libz3, "Z3_mk_set_del")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_set_union =
    Dyn.dlsym(libz3, "Z3_mk_set_union")
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_set_intersect =
    Dyn.dlsym(libz3, "Z3_mk_set_intersect")
    : _import (Z3_context, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_set_difference =
    Dyn.dlsym(libz3, "Z3_mk_set_difference")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_set_complement =
    Dyn.dlsym(libz3, "Z3_mk_set_complement")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_set_member =
    Dyn.dlsym(libz3, "Z3_mk_set_member")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_set_subset =
    Dyn.dlsym(libz3, "Z3_mk_set_subset")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

end (* local *)
end

