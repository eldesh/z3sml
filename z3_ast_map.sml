
structure Z3_Ast_Map =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context    = unit ptr
  type Z3_ast        = unit ptr
  type Z3_ast_vector = unit ptr
  type Z3_ast_map    = unit ptr
  type Z3_string     = String.string
  type Z3_bool          = int

  val Z3_mk_ast_map =
    Dyn.dlsym(libz3, "Z3_mk_ast_map")
    : _import Z3_context -> Z3_ast_map

  val Z3_ast_map_inc_ref =
    Dyn.dlsym(libz3, "Z3_ast_map_inc_ref")
    : _import (Z3_context, Z3_ast_map) -> ()

  val Z3_ast_map_dec_ref =
    Dyn.dlsym(libz3, "Z3_ast_map_dec_ref")
    : _import (Z3_context, Z3_ast_map) -> ()

  val Z3_ast_map_contains =
    Dyn.dlsym(libz3, "Z3_ast_map_contains")
    : _import (Z3_context, Z3_ast_map, Z3_ast) -> Z3_bool

  val Z3_ast_map_find =
    Dyn.dlsym(libz3, "Z3_ast_map_find")
    : _import (Z3_context, Z3_ast_map, Z3_ast) -> Z3_ast

  val Z3_ast_map_insert =
    Dyn.dlsym(libz3, "Z3_ast_map_insert")
    : _import (Z3_context, Z3_ast_map, Z3_ast, Z3_ast) -> ()

  val Z3_ast_map_erase =
    Dyn.dlsym(libz3, "Z3_ast_map_erase")
    : _import (Z3_context, Z3_ast_map, Z3_ast) -> ()

  val Z3_ast_map_reset =
    Dyn.dlsym(libz3, "Z3_ast_map_reset")
    : _import (Z3_context, Z3_ast_map) -> ()

  val Z3_ast_map_size =
    Dyn.dlsym(libz3, "Z3_ast_map_size")
    : _import (Z3_context, Z3_ast_map) -> word

  val Z3_ast_map_keys =
    Dyn.dlsym(libz3, "Z3_ast_map_keys")
    : _import (Z3_context, Z3_ast_map) -> Z3_ast_vector

  val Z3_ast_map_to_string =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_ast_map_to_string")
     : _import (Z3_context, Z3_ast_map) -> char ptr )

end (* local *)
end

