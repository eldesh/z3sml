
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

  fun Z3_mk_tuple_sort (c, mk_tuple_name, field_names, field_sorts
                        , mk_tuple_decl, proj_decl) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_tuple_sort"))
    ( c : Z3_context
    , mk_tuple_name : Z3_symbol
    , Vector.length field_names : int
    , field_names : Z3_symbol vector
    , field_sorts : Z3_sort vector
    , mk_tuple_decl : Z3_func_decl ref
    , proj_decl : Z3_func_decl array
    ) : Z3_sort

  fun Z3_mk_enumeration_sort (c, name, enum_names, enum_consts, enum_testers) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_enumeration_sort"))
    ( c : Z3_context
    , name : Z3_symbol
    , Vector.length enum_names : int
    , enum_names : Z3_symbol vector
    , enum_consts : Z3_func_decl array
    , enum_testers : Z3_func_decl array
    ) : Z3_sort

  val Z3_mk_list_sort =
    Dyn.dlsym (libz3, "Z3_mk_list_sort")
    : _import (Z3_context, Z3_symbol, Z3_sort
                , Z3_func_decl ref, Z3_func_decl ref
                , Z3_func_decl ref, Z3_func_decl ref
                , Z3_func_decl ref, Z3_func_decl ref
                ) -> Z3_sort

  fun Z3_mk_constructor (c, name, recognizer, field_names, sorts, sort_refs) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_constructor"))
    ( c : Z3_context
    , name : Z3_symbol
    , recognizer : Z3_symbol
    , Vector.length field_names : int
    , field_names : Z3_symbol vector
    , sorts : Z3_sort_opt vector
    , sort_refs : word vector
    ) : Z3_constructor

  val Z3_del_constructor =
    Dyn.dlsym (libz3, "Z3_del_constructor")
    : _import (Z3_context, Z3_constructor) -> ()

  fun Z3_mk_datatype (c, name, constructors) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_datatype"))
    ( c : Z3_context
    , name : Z3_symbol
    , Array.length constructors : int
    , constructors : Z3_constructor array) : Z3_sort

  fun Z3_mk_constructor_list (c, constructors) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_constructor_list"))
    ( c : Z3_context
    , Vector.length constructors : int
    , constructors : Z3_constructor vector) : Z3_constructor_list

  val Z3_del_constructor_list =
    Dyn.dlsym (libz3, "Z3_del_constructor_list")
    : _import (Z3_context, Z3_constructor_list) -> ()

  fun Z3_mk_datatypes (c, sort_names, sorts, constructor_list) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_datatypes"))
    ( c : Z3_context
    , Vector.length sort_names : int
    , sort_names : Z3_symbol vector
    , sorts : Z3_sort array
    , constructor_list : Z3_constructor_list array) : ()

  fun Z3_query_constructor (c, constr, constructor, tester, accessors) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_query_constructor"))
    ( c : Z3_context
    , constr : Z3_constructor
    , Array.length accessors : int
    , constructor : Z3_func_decl ref
    , tester : Z3_func_decl ref
    , accessors : Z3_func_decl array) : ()

end (* local *)
end

