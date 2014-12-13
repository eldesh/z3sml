
structure Z3_Sort =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context          = unit ptr
  type Z3_params           = unit ptr
  type Z3_sort             = unit ptr
  type Z3_symbol           = unit ptr
  type Z3_func_decl        = unit ptr
  type Z3_sort_opt         = unit ptr
  type Z3_constructor      = unit ptr
  type Z3_constructor_list = unit ptr
 
  val Z3_mk_uninterpreted_sort =
    Dyn.dlsym (libz3, "Z3_mk_uninterpreted_sort")
    : _import (Z3_context, Z3_symbol) -> Z3_sort

  val Z3_mk_bool_sort =
    Dyn.dlsym (libz3, "Z3_mk_bool_sort")
    : _import Z3_context -> Z3_sort

  val Z3_mk_int_sort =
    Dyn.dlsym (libz3, "Z3_mk_int_sort")
    : _import Z3_context -> Z3_sort

  val Z3_mk_real_sort =
    Dyn.dlsym (libz3, "Z3_mk_real_sort")
    : _import Z3_context -> Z3_sort

  val Z3_mk_bv_sort =
    Dyn.dlsym (libz3, "Z3_mk_bv_sort")
    : _import (Z3_context, Word32.word) -> Z3_sort

  (*
  val Z3_mk_finite_domain_sort =
    Dyn.dlsym (libz3, "Z3_mk_bv_sort")
    : _import (Z3_context, Z3_symbol, Word64.word) -> Z3_sort
   *)

  val Z3_mk_array_sort =
    Dyn.dlsym (libz3, "Z3_mk_array_sort")
    : _import (Z3_context, Z3_sort, Z3_sort) -> Z3_sort

  val Z3_mk_tuple_sort =
    Dyn.dlsym (libz3, "Z3_mk_tuple_sort")
    : _import (Z3_context, Z3_sort, word
                , Z3_symbol vector, Z3_sort vector
                , Z3_func_decl ref, Z3_func_decl array
                ) -> Z3_sort

  val Z3_mk_enumeration_sort =
    Dyn.dlsym (libz3, "Z3_mk_enumeration_sort")
    : _import (Z3_context, Z3_symbol, word
                , Z3_symbol vector, Z3_func_decl array
                , Z3_func_decl array
                ) -> Z3_sort

  val Z3_mk_list_sort =
    Dyn.dlsym (libz3, "Z3_mk_list_sort")
    : _import (Z3_context, Z3_symbol, Z3_sort
                , Z3_func_decl ref, Z3_func_decl ref
                , Z3_func_decl ref, Z3_func_decl ref
                , Z3_func_decl ref, Z3_func_decl ref
                ) -> Z3_sort

  val Z3_mk_constructor =
    Dyn.dlsym (libz3, "Z3_mk_constructor")
    : _import (Z3_context, Z3_symbol, Z3_symbol, word
                , Z3_symbol vector, Z3_sort_opt vector, word array
                ) -> Z3_constructor

  val Z3_del_constructor =
    Dyn.dlsym (libz3, "Z3_del_constructor")
    : _import (Z3_context, Z3_constructor) -> ()

  val Z3_mk_datatype =
    Dyn.dlsym (libz3, "Z3_mk_datatype")
    : _import (Z3_context, Z3_symbol, word
                , Z3_constructor array
                ) -> Z3_sort

  val Z3_mk_constructor_list =
    Dyn.dlsym (libz3, "Z3_mk_constructor_list")
    : _import (Z3_context, word, Z3_constructor vector) -> Z3_constructor_list

  val Z3_del_constructor_list =
    Dyn.dlsym (libz3, "Z3_del_constructor_list")
    : _import (Z3_context, Z3_constructor_list) -> ()

  val Z3_mk_datatypes =
    Dyn.dlsym (libz3, "Z3_mk_datatypes")
    : _import (Z3_context, word, Z3_symbol vector
                , Z3_sort array, Z3_constructor_list array
                ) -> ()

  val Z3_query_constructor =
    Dyn.dlsym (libz3, "Z3_query_constructor")
    : _import (Z3_context, Z3_constructor, word
                , Z3_func_decl ref, Z3_func_decl ref
                , Z3_func_decl array) -> ()

end (* local *)
end

