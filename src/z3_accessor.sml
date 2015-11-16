
structure Z3_Accessor =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context      = unit ptr
  type Z3_symbol       = unit ptr
  type Z3_sort         = unit ptr
  type Z3_ast          = unit ptr
  type Z3_func_decl    = unit ptr
  type Z3_app          = unit ptr
  type Z3_pattern      = unit ptr
  type Z3_param_descrs = unit ptr
  type Z3_params       = unit ptr

  type Z3_string         = String.string
  type Z3_bool           = Z3_bool.t

  val Z3_get_symbol_kind =
    Z3_symbol_kind.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_symbol_kind")
    : _import (Z3_context, Z3_symbol) -> int)

  val Z3_get_symbol_int =
    Dyn.dlsym(libz3, "Z3_get_symbol_int")
    : _import (Z3_context, Z3_symbol) -> int

  val Z3_get_symbol_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_get_symbol_string")
     : _import (Z3_context, Z3_symbol) -> char ptr)

  val Z3_get_sort_name =
    Dyn.dlsym(libz3, "Z3_get_sort_name")
    : _import (Z3_context, Z3_sort) -> Z3_symbol

  val Z3_get_sort_id =
    Dyn.dlsym(libz3, "Z3_get_sort_id")
    : _import (Z3_context, Z3_sort) -> word

  val Z3_sort_to_ast =
    Dyn.dlsym(libz3, "Z3_sort_to_ast")
    : _import (Z3_context, Z3_sort) -> Z3_ast

  val Z3_is_eq_sort =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_eq_sort")
       : _import (Z3_context, Z3_sort, Z3_sort) -> int)

  val Z3_get_sort_kind =
    Z3_sort_kind.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_sort_kind")
    : _import (Z3_context, Z3_sort) -> int)

  val Z3_get_bv_sort_size =
    Dyn.dlsym(libz3, "Z3_get_bv_sort_size")
    : _import (Z3_context, Z3_sort) -> word

(*
  val Z3_get_finite_domain_sort_size =
    Dyn.dlsym(libz3, "Z3_get_finite_domain_sort_size")
    : _import (Z3_context, Z3_sort, Word64.word ref) -> Z3_bool
    *)

  val Z3_get_array_sort_domain =
    Dyn.dlsym(libz3, "Z3_get_array_sort_domain")
    : _import (Z3_context, Z3_sort) -> Z3_sort

  val Z3_get_array_sort_range =
    Dyn.dlsym(libz3, "Z3_get_array_sort_range")
    : _import (Z3_context, Z3_sort) -> Z3_sort

  val Z3_get_tuple_sort_mk_decl =
    Dyn.dlsym(libz3, "Z3_get_tuple_sort_mk_decl")
    : _import (Z3_context, Z3_sort) -> Z3_func_decl

  val Z3_get_tuple_sort_num_fields =
    Dyn.dlsym(libz3, "Z3_get_tuple_sort_num_fields")
    : _import (Z3_context, Z3_sort) -> word

  val Z3_get_tuple_sort_field_decl =
    Dyn.dlsym(libz3, "Z3_get_tuple_sort_field_decl")
    : _import (Z3_context, Z3_sort, word) -> Z3_func_decl

  val Z3_get_datatype_sort_num_constructors =
    Dyn.dlsym(libz3, "Z3_get_datatype_sort_num_constructors")
    : _import (Z3_context, Z3_sort) -> word

  val Z3_get_datatype_sort_constructor =
    Dyn.dlsym(libz3, "Z3_get_datatype_sort_constructor")
    : _import (Z3_context, Z3_sort, word) -> Z3_func_decl

  val Z3_get_datatype_sort_recognizer =
    Dyn.dlsym(libz3, "Z3_get_datatype_sort_recognizer")
    : _import (Z3_context, Z3_sort, word) -> Z3_func_decl

  val Z3_get_datatype_sort_constructor_accessor =
    Dyn.dlsym(libz3, "Z3_get_datatype_sort_constructor_accessor")
    : _import (Z3_context, Z3_sort, word, word) -> Z3_func_decl

  val Z3_get_relation_arity =
    Dyn.dlsym(libz3, "Z3_get_relation_arity")
    : _import (Z3_context, Z3_sort) -> word

  val Z3_get_relation_column =
    Dyn.dlsym(libz3, "Z3_get_relation_column")
    : _import (Z3_context, Z3_sort, word) -> Z3_sort

  val Z3_func_decl_to_ast =
    Dyn.dlsym(libz3, "Z3_func_decl_to_ast")
    : _import (Z3_context, Z3_func_decl) -> Z3_ast

  val Z3_is_eq_func_decl =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_eq_func_decl")
       : _import (Z3_context, Z3_func_decl, Z3_func_decl) -> int)

  val Z3_get_func_decl_id =
    Dyn.dlsym(libz3, "Z3_get_func_decl_id")
    : _import (Z3_context, Z3_func_decl) -> word

  val Z3_get_decl_name =
    Dyn.dlsym(libz3, "Z3_get_decl_name")
    : _import (Z3_context, Z3_func_decl) -> Z3_symbol

  val Z3_get_decl_kind =
    Z3_decl_kind.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_decl_kind")
    : _import (Z3_context, Z3_func_decl) -> int)

  val Z3_get_domain_size =
    Dyn.dlsym(libz3, "Z3_get_domain_size")
    : _import (Z3_context, Z3_func_decl) -> word

  val Z3_get_arity =
    Dyn.dlsym(libz3, "Z3_get_arity")
    : _import (Z3_context, Z3_func_decl) -> word

  val Z3_get_domain =
    Dyn.dlsym(libz3, "Z3_get_domain")
    : _import (Z3_context, Z3_func_decl, word) -> Z3_sort

  val Z3_get_range =
    Dyn.dlsym(libz3, "Z3_get_range")
    : _import (Z3_context, Z3_func_decl) -> Z3_sort

  val Z3_get_decl_num_parameters =
    Dyn.dlsym(libz3, "Z3_get_decl_num_parameters")
    : _import (Z3_context, Z3_func_decl) -> word

  val Z3_get_decl_parameter_kind =
    Z3_parameter_kind.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_decl_parameter_kind")
    : _import (Z3_context, Z3_func_decl, word) -> int)

  val Z3_get_decl_int_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_int_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> int

  val Z3_get_decl_double_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_double_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> real

  val Z3_get_decl_symbol_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_symbol_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> Z3_symbol

  val Z3_get_decl_sort_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_sort_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> Z3_sort

  val Z3_get_decl_ast_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_ast_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> Z3_ast

  val Z3_get_decl_func_decl_parameter =
    Dyn.dlsym(libz3, "Z3_get_decl_func_decl_parameter")
    : _import (Z3_context, Z3_func_decl, word) -> Z3_func_decl

  val Z3_get_decl_rational_parameter =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_get_decl_rational_parameter")
     : _import (Z3_context, Z3_func_decl, word) -> char ptr)

  val Z3_app_to_ast =
    Dyn.dlsym(libz3, "Z3_app_to_ast")
    : _import (Z3_context, Z3_app) -> Z3_ast

  val Z3_get_app_decl =
    Dyn.dlsym(libz3, "Z3_get_app_decl")
    : _import (Z3_context, Z3_app) -> Z3_func_decl

  val Z3_get_app_num_args =
    Dyn.dlsym(libz3, "Z3_get_app_num_args")
    : _import (Z3_context, Z3_app) -> word

  val Z3_get_app_arg =
    Dyn.dlsym(libz3, "Z3_get_app_arg")
    : _import (Z3_context, Z3_app, word) -> Z3_ast

  val Z3_is_eq_ast =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_eq_ast")
       : _import (Z3_context, Z3_ast, Z3_ast) -> int)

  val Z3_get_ast_id =
    Dyn.dlsym(libz3, "Z3_get_ast_id")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_ast_hash =
    Dyn.dlsym(libz3, "Z3_get_ast_hash")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_sort =
    Dyn.dlsym(libz3, "Z3_get_sort")
    : _import (Z3_context, Z3_ast) -> Z3_sort

  val Z3_is_well_sorted =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_well_sorted")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_get_bool_value =
    Z3_lbool.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_bool_value")
    : _import (Z3_context, Z3_ast) -> int)

  val Z3_get_ast_kind =
    Z3_ast_kind.fromInt o (
    Dyn.dlsym(libz3, "Z3_get_ast_kind")
    : _import (Z3_context, Z3_ast) -> int)

  val Z3_is_app =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_app")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_is_numeral_ast =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_numeral_ast")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_is_algebraic_number =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_algebraic_number")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_to_app =
    Dyn.dlsym(libz3, "Z3_to_app")
    : _import (Z3_context, Z3_ast) -> Z3_app

  val Z3_to_func_decl =
    Dyn.dlsym(libz3, "Z3_to_func_decl")
    : _import (Z3_context, Z3_ast) -> Z3_func_decl

  val Z3_get_numeral_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_get_numeral_string")
     : _import (Z3_context, Z3_ast) -> char ptr)

  val Z3_get_numeral_decimal_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_get_numeral_decimal_string")
     : _import (Z3_context, Z3_ast, word) -> char ptr)

  val Z3_get_numerator =
    Dyn.dlsym(libz3, "Z3_get_numerator")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_get_denominator =
    Dyn.dlsym(libz3, "Z3_get_denominator")
    : _import (Z3_context, Z3_ast) -> Z3_ast

(*
  val Z3_get_numeral_small =
    Dyn.dlsym(libz3, "Z3_get_numeral_small")
    : _import (Z3_context, Z3_ast, Int64.int ref, Int64.int ref) -> Z3_bool
 *)

  val Z3_get_numeral_int =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_get_numeral_int")
       : _import (Z3_context, Z3_ast, int ref) -> int)

  val Z3_get_numeral_uint =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_get_numeral_uint")
       : _import (Z3_context, Z3_ast, word ref) -> int)

(*
  val Z3_get_numeral_uint64 =
    Dyn.dlsym(libz3, "Z3_get_numeral_uint64")
    : _import (Z3_context, Z3_ast, Word64.word ref) -> Z3_bool

  val Z3_get_numeral_int64 =
    Dyn.dlsym(libz3, "Z3_get_numeral_int64")
    : _import (Z3_context, Z3_ast, Int64.int ref) -> Z3_bool

  val Z3_get_numeral_rational_int64 =
    Dyn.dlsym(libz3, "Z3_get_numeral_rational_int64")
    : _import (Z3_context, Z3_ast, Int64.int ref, Int64.int ref) ->
    Z3_bool
    *)

  val Z3_get_algebraic_number_lower =
    Dyn.dlsym(libz3, "Z3_get_algebraic_number_lower")
    : _import (Z3_context, Z3_ast, word) -> Z3_ast

  val Z3_get_algebraic_number_upper =
    Dyn.dlsym(libz3, "Z3_get_algebraic_number_upper")
    : _import (Z3_context, Z3_ast, word) -> Z3_ast

  val Z3_pattern_to_ast =
    Dyn.dlsym(libz3, "Z3_pattern_to_ast")
    : _import (Z3_context, Z3_pattern) -> Z3_ast

  val Z3_get_pattern_num_terms =
    Dyn.dlsym(libz3, "Z3_get_pattern_num_terms")
    : _import (Z3_context, Z3_pattern) -> word

  val Z3_get_pattern =
    Dyn.dlsym(libz3, "Z3_get_pattern")
    : _import (Z3_context, Z3_pattern, word) -> Z3_ast

  val Z3_get_index_value =
    Dyn.dlsym(libz3, "Z3_get_index_value")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_is_quantifier_forall =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_is_quantifier_forall")
       : _import (Z3_context, Z3_ast) -> int)

  val Z3_get_quantifier_weight =
    Dyn.dlsym(libz3, "Z3_get_quantifier_weight")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_quantifier_num_patterns =
    Dyn.dlsym(libz3, "Z3_get_quantifier_num_patterns")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_quantifier_pattern_ast =
    Dyn.dlsym(libz3, "Z3_get_quantifier_pattern_ast")
    : _import (Z3_context, Z3_ast, word) -> Z3_pattern

  val Z3_get_quantifier_num_no_patterns =
    Dyn.dlsym(libz3, "Z3_get_quantifier_num_no_patterns")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_quantifier_no_pattern_ast =
    Dyn.dlsym(libz3, "Z3_get_quantifier_no_pattern_ast")
    : _import (Z3_context, Z3_ast, word) -> Z3_ast

  val Z3_get_quantifier_num_bound =
    Dyn.dlsym(libz3, "Z3_get_quantifier_num_bound")
    : _import (Z3_context, Z3_ast) -> word

  val Z3_get_quantifier_bound_name =
    Dyn.dlsym(libz3, "Z3_get_quantifier_bound_name")
    : _import (Z3_context, Z3_ast, word) -> Z3_symbol

  val Z3_get_quantifier_bound_sort =
    Dyn.dlsym(libz3, "Z3_get_quantifier_bound_sort")
    : _import (Z3_context, Z3_ast, word) -> Z3_sort

  val Z3_get_quantifier_body =
    Dyn.dlsym(libz3, "Z3_get_quantifier_body")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_simplify =
    Dyn.dlsym(libz3, "Z3_simplify")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_simplify_ex =
    Dyn.dlsym(libz3, "Z3_simplify_ex")
    : _import (Z3_context, Z3_ast, Z3_params) -> Z3_ast

  val Z3_simplify_get_help =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_simplify_get_help")
     : _import Z3_context -> char ptr)

  val Z3_simplify_get_param_descrs =
    Dyn.dlsym(libz3, "Z3_simplify_get_param_descrs")
    : _import Z3_context -> Z3_param_descrs

end (* local *)
end

