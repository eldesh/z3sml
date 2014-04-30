
(*
 * Z3 wrapper structure to SML# 2.0.0
 * 
 * ref. http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html
 *)
structure Z3 =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_config  = unit ptr

  type Z3_symbol       = unit ptr
  type Z3_ast          = unit ptr
  type Z3_sort         = unit ptr
  type Z3_func_decl    = unit ptr
  type Z3_app          = unit ptr
  type Z3_pattern      = unit ptr
  type Z3_params       = unit ptr
  type Z3_model        = unit ptr
  type Z3_func_interp  = unit ptr
  type Z3_func_entry   = unit ptr
  type Z3_fixedpoint   = unit ptr
  type Z3_ast_vector   = unit ptr
  type Z3_ast_map      = unit ptr
  type Z3_tactic       = unit ptr
  type Z3_probe        = unit ptr
  type Z3_apply_result = unit ptr
  type Z3_solver       = unit ptr
  type Z3_stats        = unit ptr

  type Z3_context       = unit ptr
  type Z3_param_kind    = unit ptr
  type Z3_error_code    = word
  type Z3_bool          = int
  type Z3_string        = string
  type Z3_string_ptr    = Z3_string ref
  type Z3_param_descrs     = unit ptr
  type Z3_constructor      = unit ptr
  type Z3_constructor_list = unit ptr
  type Z3_sort_opt         = unit ptr
  type Z3_ast_print_mode   = unit ptr
  type Z3_contextarget     = unit ptr
  type Z3_ast_kind         = int
  type Z3_symbol_kind      = int
  type Z3_parameter_kind   = int
  type Z3_sort_kind        = int
  type Z3_ast_kind         = int
  type Z3_decl_kind        = int
  type Z3_theory           = unit ptr
  type Z3_theory_data      = unit ptr
  type Z3_ast_vector       = unit ptr

  open Z3_enum

  type Z3_error_handler = Z3_context * Z3_error_code -> unit

  val Z3_TRUE : Z3_bool = 1
  val Z3_FALSe : Z3_bool = 0

  val Z3_mk_config =
    Dyn.dlsym (libz3, "Z3_mk_config")
    : _import () -> Z3_config

  val Z3_del_config =
    Dyn.dlsym (libz3, "Z3_del_config")
    : _import Z3_config -> ()

  val Z3_set_param_value =
    Dyn.dlsym (libz3, "Z3_set_param_value")
    : _import (Z3_config, Z3_string, Z3_string) -> ()

  val Z3_mk_context =
    Dyn.dlsym (libz3, "Z3_mk_context")
    : _import Z3_config -> Z3_context

  val Z3_mk_context_rc =
    Dyn.dlsym (libz3, "Z3_mk_context_rc")
    : _import Z3_config -> Z3_context

  val Z3_del_context =
    Dyn.dlsym (libz3, "Z3_del_context")
    : _import Z3_context -> ()

  val Z3_inc_ref =
    Dyn.dlsym (libz3, "Z3_inc_ref")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_dec_ref =
    Dyn.dlsym (libz3, "Z3_dec_ref")
    : _import (Z3_context, Z3_ast) -> ()

  val Z3_update_param_value =
    Dyn.dlsym (libz3, "Z3_update_param_value")
    : _import (Z3_context, Z3_string, Z3_string) -> ()

  val Z3_get_param_value =
    Dyn.dlsym (libz3, "Z3_get_param_value")
    : _import (Z3_context, Z3_string, Z3_string ref) -> Z3_bool

  val Z3_interrupt =
    Dyn.dlsym (libz3, "Z3_interrupt")
    : _import Z3_context -> ()

  (**
   * Parameters
   *)
  val Z3_mk_params =
    Dyn.dlsym (libz3, "Z3_mk_params")
    : _import Z3_context -> Z3_params

  val Z3_params_inc_ref =
    Dyn.dlsym (libz3, "Z3_params_inc_ref")
    : _import (Z3_context, Z3_params) -> ()

  val Z3_params_dec_ref =
    Dyn.dlsym (libz3, "Z3_params_dec_ref")
    : _import (Z3_context, Z3_params) -> ()

  val Z3_params_set_bool =
    Dyn.dlsym (libz3, "Z3_params_set_bool")
    : _import (Z3_context, Z3_params, Z3_symbol, Z3_bool) -> ()

  val Z3_params_set_uint =
    Dyn.dlsym (libz3, "Z3_params_set_uint")
    : _import (Z3_context, Z3_params, Z3_symbol, Word32.word) -> ()

  val Z3_params_set_double =
    Dyn.dlsym (libz3, "Z3_params_set_double")
    : _import (Z3_context, Z3_params, Z3_symbol, Real.real) -> ()

  val Z3_params_set_symbol =
    Dyn.dlsym (libz3, "Z3_params_set_symbol")
    : _import (Z3_context, Z3_params, Z3_symbol, Z3_symbol) -> ()

  val Z3_params_to_string =
    Ptr.importString o
    ( Dyn.dlsym (libz3, "Z3_params_to_string")
      : _import (Z3_context, Z3_params) -> char ptr
      )

  val Z3_params_validate =
    Dyn.dlsym (libz3, "Z3_params_validate")
    : _import (Z3_context, Z3_params, Z3_param_descrs) -> ()

  (**
   *  Parameter Descriptions
   *)
  val Z3_param_descrs_inc_ref =
    Dyn.dlsym (libz3, "Z3_param_descrs_inc_ref")
    : _import (Z3_context, Z3_param_descrs) -> ()

  val Z3_param_descrs_dec_ref =
    Dyn.dlsym (libz3, "Z3_param_descrs_dec_ref")
    : _import (Z3_context, Z3_param_descrs) -> ()

  val Z3_param_descrs_get_kind =
    Dyn.dlsym (libz3, "Z3_param_descrs_get_kind")
    : _import (Z3_context, Z3_param_descrs, Z3_symbol) -> Z3_param_kind

  val Z3_param_descrs_size =
    Dyn.dlsym (libz3, "Z3_param_descrs_get_kind")
    : _import (Z3_context, Z3_param_descrs) -> Word32.word

  val Z3_param_descrs_get_name =
    Dyn.dlsym (libz3, "Z3_param_descrs_get_name")
    : _import (Z3_context, Z3_param_descrs, word) -> Z3_symbol

  val Z3_param_descrs_to_string =
    Ptr.importString o
    ( Dyn.dlsym (libz3, "Z3_param_descrs_to_string")
      : _import (Z3_context, Z3_param_descrs) -> char ptr
      )

  (**
   *  Symbols
   *)
  val Z3_mk_int_symbol =
    Dyn.dlsym (libz3, "Z3_mk_int_symbol")
    : _import (Z3_context, int) -> Z3_symbol

  val Z3_mk_string_symbol =
    Dyn.dlsym (libz3, "Z3_mk_string_symbol")
    : _import (Z3_context, Z3_string) -> Z3_symbol

  (**
   *  Sort
   *)
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

  (**
   * Constans and Applications
   *)
  val Z3_mk_func_decl =
    Dyn.dlsym (libz3, "Z3_mk_func_decl")
    : _import (Z3_context, Z3_symbol, word, Z3_sort vector, Z3_sort) -> Z3_func_decl

  val Z3_mk_app =
    Dyn.dlsym (libz3, "Z3_mk_app")
    : _import (Z3_context, Z3_func_decl, word, Z3_ast vector) -> Z3_func_decl

  val Z3_mk_const =
    Dyn.dlsym (libz3, "Z3_mk_const")
    : _import (Z3_context, Z3_symbol, Z3_sort) -> Z3_ast

  val Z3_mk_fresh_func_decl =
    Dyn.dlsym (libz3, "Z3_mk_fresh_func_decl")
    : _import (Z3_context, Z3_string, word, Z3_sort vector, Z3_sort) -> Z3_func_decl

  val Z3_mk_fresh_const =
    Dyn.dlsym (libz3, "Z3_mk_fresh_const")
    : _import (Z3_context, Z3_string, Z3_sort) -> Z3_ast

  (**
   * Propositional Logic and Equality
   *)
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

  (**
   * Arithmetic: Integers and Reals
   *)
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

  (**
   * Bit-vectors
   *)
  val Z3_mk_bvnot =
    Dyn.dlsym(libz3, "Z3_mk_bvnot")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_bvredand =
    Dyn.dlsym(libz3, "Z3_mk_bvredand")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_bvredor =
    Dyn.dlsym(libz3, "Z3_mk_bvredor")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_bvand =
    Dyn.dlsym(libz3, "Z3_mk_bvand")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvor =
    Dyn.dlsym(libz3, "Z3_mk_bvor")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvxor =
    Dyn.dlsym(libz3, "Z3_mk_bvxor")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvnand =
    Dyn.dlsym(libz3, "Z3_mk_bvnand")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvnor =
    Dyn.dlsym(libz3, "Z3_mk_bvnor")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvxnor =
    Dyn.dlsym(libz3, "Z3_mk_bvxnor")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvneg =
    Dyn.dlsym(libz3, "Z3_mk_bvneg")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_bvadd =
    Dyn.dlsym(libz3, "Z3_mk_bvadd")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsub =
    Dyn.dlsym(libz3, "Z3_mk_bvsub")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvmul =
    Dyn.dlsym(libz3, "Z3_mk_bvmul")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvudiv =
    Dyn.dlsym(libz3, "Z3_mk_bvudiv")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsdiv =
    Dyn.dlsym(libz3, "Z3_mk_bvsdiv")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvurem =
    Dyn.dlsym(libz3, "Z3_mk_bvurem")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsrem =
    Dyn.dlsym(libz3, "Z3_mk_bvsrem")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsmod =
    Dyn.dlsym(libz3, "Z3_mk_bvsmod")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvult =
    Dyn.dlsym(libz3, "Z3_mk_bvult")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvslt =
    Dyn.dlsym(libz3, "Z3_mk_bvslt")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvule =
    Dyn.dlsym(libz3, "Z3_mk_bvule")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsle =
    Dyn.dlsym(libz3, "Z3_mk_bvsle")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvuge =
    Dyn.dlsym(libz3, "Z3_mk_bvuge")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsge =
    Dyn.dlsym(libz3, "Z3_mk_bvsge")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvugt =
    Dyn.dlsym(libz3, "Z3_mk_bvugt")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsgt =
    Dyn.dlsym(libz3, "Z3_mk_bvsgt")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_concat =
    Dyn.dlsym(libz3, "Z3_mk_concat")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_extract =
    Dyn.dlsym(libz3, "Z3_mk_extract")
    : _import (Z3_context, word, word, Z3_ast) -> Z3_ast

  val Z3_mk_sign_ext =
    Dyn.dlsym(libz3, "Z3_mk_sign_ext")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_zero_ext =
    Dyn.dlsym(libz3, "Z3_mk_zero_ext")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_repeat =
    Dyn.dlsym(libz3, "Z3_mk_repeat")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_bvshl =
    Dyn.dlsym(libz3, "Z3_mk_bvshl")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvlshr =
    Dyn.dlsym(libz3, "Z3_mk_bvlshr")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvashr =
    Dyn.dlsym(libz3, "Z3_mk_bvashr")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_rotate_left =
    Dyn.dlsym(libz3, "Z3_mk_rotate_left")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_rotate_right =
    Dyn.dlsym(libz3, "Z3_mk_rotate_right")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_ext_rotate_left =
    Dyn.dlsym(libz3, "Z3_mk_ext_rotate_left")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_ext_rotate_right =
    Dyn.dlsym(libz3, "Z3_mk_ext_rotate_right")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_int2bv =
    Dyn.dlsym(libz3, "Z3_mk_int2bv")
    : _import (Z3_context, word, Z3_ast) -> Z3_ast

  val Z3_mk_bv2int =
    Dyn.dlsym(libz3, "Z3_mk_bv2int")
    : _import (Z3_context, Z3_ast, Z3_bool) -> Z3_ast

  val Z3_mk_bvadd_no_overflow =
    Dyn.dlsym(libz3, "Z3_mk_bvadd_no_overflow")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_bool) -> Z3_ast

  val Z3_mk_bvadd_no_underflow =
    Dyn.dlsym(libz3, "Z3_mk_bvadd_no_underflow")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsub_no_overflow =
    Dyn.dlsym(libz3, "Z3_mk_bvsub_no_overflow")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvsub_no_underflow =
    Dyn.dlsym(libz3, "Z3_mk_bvsub_no_underflow")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_bool) -> Z3_ast

  val Z3_mk_bvsdiv_no_overflow =
    Dyn.dlsym(libz3, "Z3_mk_bvsdiv_no_overflow")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_bvneg_no_overflow =
    Dyn.dlsym(libz3, "Z3_mk_bvneg_no_overflow")
    : _import (Z3_context, Z3_ast) -> Z3_ast

  val Z3_mk_bvmul_no_overflow =
    Dyn.dlsym(libz3, "Z3_mk_bvmul_no_overflow")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_bool) -> Z3_ast

  val Z3_mk_bvmul_no_underflow =
    Dyn.dlsym(libz3, "Z3_mk_bvmul_no_underflow")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  (**
   * Arrays
   *)
  val Z3_mk_select =
    Dyn.dlsym(libz3, "Z3_mk_select")
    : _import (Z3_context, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_store =
    Dyn.dlsym(libz3, "Z3_mk_store")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_ast) -> Z3_ast

  val Z3_mk_const_array =
    Dyn.dlsym(libz3, "Z3_mk_const_array")
    : _import (Z3_context, Z3_sort, Z3_ast) -> Z3_ast

  val Z3_mk_map =
    Dyn.dlsym(libz3, "Z3_mk_map")
    : _import (Z3_context, Z3_func_decl, word, Z3_ast vector) -> Z3_ast

  val Z3_mk_array_default =
    Dyn.dlsym(libz3, "Z3_mk_array_default")
    : _import (Z3_context, Z3_ast array) -> Z3_ast

  (**
   * Sets
   *)
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
    : _import (Z3_context, word, Z3_ast array) -> Z3_ast

  val Z3_mk_set_intersect =
    Dyn.dlsym(libz3, "Z3_mk_set_intersect")
    : _import (Z3_context, word, Z3_ast array) -> Z3_ast

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

  (**
   * Numerals
   *)
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

  (**
   * Quantifiers
   *)
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

  (**
   * Accessors
   *)
  structure Accessor = Z3_Accessor

  (**
   * Modifiers
   *)
  val Z3_update_term =
    Dyn.dlsym(libz3, "Z3_update_term")
    : _import (Z3_context, Z3_ast, word, Z3_ast array) -> Z3_ast

  val Z3_substitute =
    Dyn.dlsym(libz3, "Z3_substitute")
    : _import (Z3_context, Z3_ast, word, Z3_ast vector, Z3_ast array) -> Z3_ast

  val Z3_substitute_vars =
    Dyn.dlsym(libz3, "Z3_substitute_vars")
    : _import (Z3_context, Z3_ast, word, Z3_ast array) -> Z3_ast

  val Z3_translate =
    Dyn.dlsym(libz3, "Z3_translate")
    : _import (Z3_context, Z3_ast, Z3_contextarget) -> Z3_ast

  (**
   * Models
   *)
  structure Model = Z3_Model

  (**
   * Interaction logging.
   *)
  val Z3_open_log =
    Dyn.dlsym(libz3, "Z3_open_log")
    : _import Z3_string -> Z3_bool

  val Z3_append_log =
    Dyn.dlsym(libz3, "Z3_append_log")
    : _import Z3_string -> ()

  val Z3_close_log =
    Dyn.dlsym(libz3, "Z3_close_log")
    : _import () -> ()

  val Z3_toggle_warning_messages =
    Dyn.dlsym(libz3, "Z3_toggle_warning_messages")
    : _import Z3_bool -> ()

  (**
   * String conversion
   *)
  val Z3_set_ast_print_mode =
    Dyn.dlsym(libz3, "Z3_set_ast_print_mode")
    : _import (Z3_context, Z3_ast_print_mode) -> ()

  val Z3_ast_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_ast_to_string")
     : _import (Z3_context, Z3_ast) -> char ptr)

  val Z3_pattern_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_pattern_to_string")
     : _import (Z3_context, Z3_pattern) -> char ptr)

  val Z3_sort_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_sort_to_string")
     : _import (Z3_context, Z3_sort) -> char ptr)

  val Z3_func_decl_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_func_decl_to_string")
     : _import (Z3_context, Z3_func_decl) -> char ptr)

  val Z3_model_to_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_model_to_string")
     : _import (Z3_context, Z3_model) -> char ptr)

  val Z3_benchmark_to_smtlib_string =
    Ptr.importString o
    (Dyn.dlsym(libz3, "Z3_benchmark_to_smtlib_string")
     : _import (Z3_context, Z3_string, Z3_string
                , Z3_string, Z3_string
                , word, Z3_ast array, Z3_ast
                ) -> char ptr)

  (**
   * Parser interface
   *)
  structure Parser = Z3_Parser

  (**
   * Error Handling
   *)
  val Z3_get_error_code =
    Dyn.dlsym(libz3, "Z3_get_error_code")
    : _import Z3_context -> Z3_error_code

  val Z3_set_error_handler =
    Dyn.dlsym(libz3, "Z3_set_error_handler")
    : _import (Z3_context, (Z3_context, Z3_error_code)->()) -> ()

  val Z3_set_error =
    Dyn.dlsym(libz3, "Z3_set_error")
    : _import (Z3_context, Z3_error_code) -> ()

  val Z3_get_error_msg =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_error_msg")
      : _import Z3_error_code -> char ptr)

  (**
   * BEGIN_MLAPI_EXCLUDE Z3_string
   *)
  val Z3_get_error_msg_ex =
    Ptr.importString o
    ( Dyn.dlsym(libz3, "Z3_get_error_msg_ex")
      : _import (Z3_context, Z3_error_code) -> char ptr)

  (**
   * Miscellaneous
   *)
  val Z3_get_version =
    Dyn.dlsym(libz3, "Z3_get_version")
    : _import (word ref, word ref, word ref, word ref) -> ()

  val Z3_enable_trace =
    Dyn.dlsym(libz3, "Z3_enable_trace")
    : _import Z3_string -> ()

  val Z3_disable_trace =
    Dyn.dlsym(libz3, "Z3_disable_trace")
    : _import Z3_string -> ()

  val Z3_reset_memory =
    Dyn.dlsym(libz3, "Z3_reset_memory")
    : _import () -> ()

  (**
   * External Theory Plugins
   *)
  structure ExternalTheoryPlugin = Z3_ExternalTheoryPlugin

  (**
   * Fixpoint facilities
   *)
  structure Fixedpoint = Z3_Fixedpoint

  (**
   * AST vectors
   *)
  structure AstVector = Z3_Ast_Vector

  (**
   * AST maps
   *)
  structure AstMap = Z3_Ast_Map

  (**
   * Goals
   *)
  structure Goal = Z3_Goal

  (**
   * Tactics and Probes
   *)
  structure TacticAndProbe = Z3_Tactic_And_Probe

  (**
   * Solvers
   *)
  structure Solver = Z3_Solver

  (**
   * Statistics
   *)
  structure Statistics = Z3_Statistics

  (**
   * Deprecxated Constraints API
   *)
  structure Deprecated =
  struct
    val Z3_check_and_get_model =
      Dyn.dlsym (libz3, "Z3_check_and_get_model")
      : _import (Z3_context, Z3_model ref) -> Z3_lbool

    val Z3_check =
      Dyn.dlsym (libz3, "Z3_check")
      : _import Z3_context -> Z3_lbool

    val Z3_del_model =
      Dyn.dlsym (libz3, "Z3_del_model")
      : _import (Z3_context, Z3_model) -> ()

    val Z3_assert_cnstr =
      Dyn.dlsym (libz3, "Z3_assert_cnstr")
      : _import (Z3_context, Z3_ast) -> ()

    val Z3_context_to_string =
      Ptr.importString o
      (Dyn.dlsym (libz3, "Z3_context_to_string")
      : _import Z3_context -> char ptr)

  end (* Deprecated *)

end (* local *)
end

