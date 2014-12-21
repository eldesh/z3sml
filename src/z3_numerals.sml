
structure Z3_Numerals =
struct
local
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_string  = string
  type Z3_sort    = unit ptr
  type Z3_ast     = unit ptr

  val Z3_mk_numeral =
    Dyn.dlsym(libz3, "Z3_mk_numeral")
    : _import (Z3_context, Z3_string, Z3_sort) -> Z3_ast

  val Z3_mk_real =
    Dyn.dlsym(libz3, "Z3_mk_real")
    : _import (Z3_context, int, int) -> Z3_ast

  val Z3_mk_int =
    Dyn.dlsym(libz3, "Z3_mk_int")
    : _import (Z3_context, int, Z3_sort) -> Z3_ast

  val Z3_mk_unsigned_int =
    Dyn.dlsym(libz3, "Z3_mk_unsigned_int")
    : _import (Z3_context, word, Z3_sort) -> Z3_ast

(*
  val Z3_mk_int64 =
    Dyn.dlsym(libz3, "Z3_mk_int64")
    : _import (Z3_context, Int64.int, Z3_sort) -> Z3_ast

  val Z3_mk_unsigned_int64 =
    Dyn.dlsym(libz3, "Z3_mk_unsigned_int64")
    : _import (Z3_context, Word64.word, Z3_sort) -> Z3_ast
 *)

end (* local *)
end

