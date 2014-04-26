
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

  type Z3_context = unit ptr
  type Z3_param_kind = unit ptr
  type Z3_error_code = word
  type Z3_error_handler = Z3_context
  type Z3_bool = int
  type Z3_string = string
  type Z3_string_ptr = Z3_string ref
  type Z3_param_descrs = unit ptr
  type Z3_constructor      = unit ptr
  type Z3_constructor_list = unit ptr
  type Z3_sort_opt         = unit ptr

  (* 
    type Z3_error_handler = (Z3_context, Ze_error_code) -> ()
  *)
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


  val Z3_set_error_handler =
    Dyn.dlsym (libz3, "Z3_set_error_handler")
    : _import (Z3_context, (Z3_context, Z3_error_code)->()) -> ()

  val Z3_context_to_string =
    Ptr.importString o
       (Dyn.dlsym (libz3, "Z3_context_to_string")
        : _import Z3_context -> char ptr
        )

  fun mk_context () =
    let
      val cfg = Z3_mk_config ()
      val () = Z3_set_param_value (cfg, "MODEL", "true");
    in
      let
        val ctx = Z3_mk_context cfg
      in
        Z3_set_error_handler (ctx, fn _=> print "error\n");
        Z3_del_config cfg;
        ctx
      end
    end

end (* local *)
end

