
signature Z3 =
sig
  type Z3_config

  type Z3_symbol
  type Z3_ast           = unit ptr
  eqtype Z3_sort
  type Z3_func_decl     = unit ptr
  type Z3_app
  type Z3_pattern
  type Z3_params
  type Z3_model         = unit ptr
  type Z3_func_interp  
  type Z3_func_entry   
  type Z3_fixedpoint   
  type Z3_ast_vector   
  type Z3_ast_map      
  type Z3_tactic       
  type Z3_probe        
  type Z3_apply_result 
  type Z3_solver       
  type Z3_stats        
  type Z3_rcf_num      
  type Z3_literals     
  type Z3_goal         

  type Z3_context          
  type Z3_sort_opt          = Z3_sort option
  type Z3_constructor      
  type Z3_constructor_list 
  type Z3_string            = String.string
  type Z3_string_ptr        = Z3_string ref
  type Z3_param_descrs     
  type Z3_contextarget     
  type Z3_theory           
  type Z3_theory_data      

  eqtype Z3_bool           
  val Z3_TRUE  : Z3_bool
  val Z3_FALSE : Z3_bool

  type Z3_error_handler = Z3_context * Z3_enum.Z3_error_code.t -> unit

  type Z3_reduce_app_callback_fptr =
         (Z3_theory * Z3_func_decl * Z3_ast vector * Z3_ast ref) -> Z3_bool

  type Z3_reduce_eq_callback_fptr =
         (Z3_theory * Z3_ast * Z3_ast * Z3_ast ref) -> Z3_bool

  type Z3_reduce_distinct_callback_fptr =
         (Z3_theory * Z3_ast vector * Z3_ast ref) -> Z3_bool

  type Z3_fixedpoint_reduce_assign_callback_fptr =
         (unit ptr * Z3_func_decl * Z3_ast vector * Z3_ast vector) -> unit

  type Z3_fixedpoint_reduce_app_callback_fptr =
         (unit ptr * Z3_func_decl * Z3_ast vector * Z3_ast ref) -> unit


  structure Enum : Z3_ENUM

  (**
   * algebraic
   *)
  structure Algebraic : (* Z3_Algebraic *)
  sig
    type Z3_context = Z3_context
    type Z3_ast     = Z3_ast
    type Z3_bool    = Z3_bool
    type Z3_ast_vector = Z3_ast_vector

    val Z3_algebraic_is_value
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_algebraic_is_pos
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_algebraic_is_neg
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_algebraic_is_zero
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_algebraic_sign
      : Z3_context * Z3_ast -> int

    val Z3_algebraic_add
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_algebraic_sub
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_algebraic_mul
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_algebraic_div
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_algebraic_root
      : Z3_context * Z3_ast * word -> Z3_ast

    val Z3_algebraic_power
      : Z3_context * Z3_ast * word -> Z3_ast

    val Z3_algebraic_lt
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_gt
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_le
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_ge
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_eq
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_neq
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_algebraic_roots
      : Z3_context * Z3_ast * word * Z3_ast array -> Z3_ast_vector

    val Z3_algebraic_eval
      : Z3_context * Z3_ast * word * Z3_ast array -> int
  end

  structure Global : (* Z3_global *)
  sig
    type Z3_bool   = Z3_bool
    type Z3_string = Z3_string

    val Z3_global_param_set
      : Z3_string * Z3_string -> unit

    val Z3_global_param_reset_all
      : unit -> unit

    val Z3_global_param_get
      : Z3_string * Z3_string ref -> Z3_bool
  end

  structure Config : (* Z3_config *)
  sig
    type Z3_config = Z3_config
    type Z3_string = Z3_string

    val Z3_mk_config
      : unit -> Z3_config

    val Z3_del_config
      : Z3_config -> unit

    val Z3_set_param_value
      : Z3_config * Z3_string * Z3_string -> unit
  end

  structure Context : (* Z3_Context *)
  sig
    type Z3_config  = Z3_config
    type Z3_context = Z3_context
    type Z3_ast     = Z3_ast
    type Z3_string  = Z3_string
    type Z3_bool    = Z3_bool

    val Z3_mk_context
      : Z3_config -> Z3_context

    val Z3_mk_context_rc
      : Z3_config -> Z3_context

    val Z3_del_context
      : Z3_context -> unit

    val Z3_inc_ref
      : Z3_context * Z3_ast -> unit

    val Z3_dec_ref
      : Z3_context * Z3_ast -> unit

    val Z3_update_param_value
      : Z3_context * Z3_string * Z3_string -> unit

    val Z3_interrupt
      : Z3_context -> unit

  end (* Context *)

  structure Parameter : (* Z3_Parameter *)
  sig
    type Z3_context      = Z3_context
    type Z3_params       = Z3_params
    type Z3_symbol       = Z3_symbol
    type Z3_param_descrs = Z3_param_descrs
    type Z3_bool         = Z3_bool
    type Z3_string       = String.string

    val Z3_mk_params
      : Z3_context -> Z3_params

    val Z3_params_inc_ref
      : Z3_context * Z3_params -> unit

    val Z3_params_dec_ref
      : Z3_context * Z3_params -> unit

    val Z3_params_set_bool
      : Z3_context * Z3_params * Z3_symbol * Z3_bool -> unit

    val Z3_params_set_uint
      : Z3_context * Z3_params * Z3_symbol * Word32.word -> unit

    val Z3_params_set_double
      : Z3_context * Z3_params * Z3_symbol * Real.real -> unit

    val Z3_params_set_symbol
      : Z3_context * Z3_params * Z3_symbol * Z3_symbol -> unit

    val Z3_params_to_string
      : Z3_context * Z3_params -> Z3_string

    val Z3_params_validate
      : Z3_context * Z3_params * Z3_param_descrs -> unit

  end (* Parameter *)

  structure ParameterDesc : (* Z3_ParameterDesc *)
  sig
    type Z3_context      = Z3_context
    type Z3_param_descrs = Z3_param_descrs
    type Z3_symbol       = Z3_symbol
    type Z3_string       = Z3_string

    val Z3_param_descrs_inc_ref
      : Z3_context * Z3_param_descrs -> unit

    val Z3_param_descrs_dec_ref
      : Z3_context * Z3_param_descrs -> unit

    val Z3_param_descrs_get_kind
      : Z3_context * Z3_param_descrs * Z3_symbol -> Enum.Z3_param_kind.t

    val Z3_param_descrs_size
      : Z3_context * Z3_param_descrs -> Word32.word

    val Z3_param_descrs_get_name
      : Z3_context * Z3_param_descrs * word -> Z3_symbol

    val Z3_param_descrs_to_string
      : Z3_context * Z3_param_descrs -> Z3_string
  end (* ParameterDesc *)

  val Z3_mk_int_symbol
    : Z3_context * int -> Z3_symbol

  val Z3_mk_string_symbol
    : Z3_context * Z3_string -> Z3_symbol

  structure Sort : (* Z3_Sort *)
  sig
    type Z3_context          = Z3_context
    type Z3_params           = Z3_params
    type Z3_sort             = Z3_sort
    type Z3_symbol           = Z3_symbol
    type Z3_func_decl        = Z3_func_decl
    type Z3_sort_opt         = Z3_sort option
    type Z3_constructor      = Z3_constructor
    type Z3_constructor_list = Z3_constructor_list

    val Z3_mk_uninterpreted_sort
      : Z3_context * Z3_symbol -> Z3_sort

    val Z3_mk_bool_sort
      : Z3_context -> Z3_sort

    val Z3_mk_int_sort
      : Z3_context -> Z3_sort

    val Z3_mk_real_sort
      : Z3_context -> Z3_sort

    val Z3_mk_bv_sort
      : Z3_context * Word32.word -> Z3_sort

    (*
    val Z3_mk_finite_domain_sort
      : Z3_context * Z3_symbol * Word64.word -> Z3_sort
     *)

    val Z3_mk_array_sort
      : Z3_context * Z3_sort * Z3_sort -> Z3_sort

    val Z3_mk_tuple_sort
      : Z3_context * Z3_symbol
                   * Z3_symbol vector * Z3_sort vector
                   * Z3_func_decl ref * Z3_func_decl array
                  -> Z3_sort

    val Z3_mk_enumeration_sort
      : Z3_context * Z3_symbol
                   * Z3_symbol vector * Z3_func_decl array
                   * Z3_func_decl array
                  -> Z3_sort

    val Z3_mk_list_sort
      : Z3_context * Z3_symbol * Z3_sort
                   * Z3_func_decl ref * Z3_func_decl ref
                   * Z3_func_decl ref * Z3_func_decl ref
                   * Z3_func_decl ref * Z3_func_decl ref
                  -> Z3_sort

    val Z3_mk_constructor
      : Z3_context * Z3_symbol * Z3_symbol
                   * Z3_symbol vector
				   * Z3_sort_opt vector
				   * word vector
                  -> Z3_constructor

    val Z3_del_constructor
      : Z3_context * Z3_constructor -> unit

    val Z3_mk_datatype
      : Z3_context * Z3_symbol
                   * Z3_constructor array
                  -> Z3_sort

    val Z3_mk_constructor_list
      : Z3_context * Z3_constructor vector -> Z3_constructor_list

    val Z3_del_constructor_list
      : Z3_context * Z3_constructor_list -> unit

    val Z3_mk_datatypes
      : Z3_context * Z3_symbol vector
                   * Z3_sort array * Z3_constructor_list array
                  -> unit

    val Z3_query_constructor
      : Z3_context * Z3_constructor
                   * Z3_func_decl ref * Z3_func_decl ref
                   * Z3_func_decl array
                 -> unit
  end (* Sort *)

  val Z3_mk_func_decl
    : Z3_context * Z3_symbol * Z3_sort vector * Z3_sort -> Z3_func_decl

  val Z3_mk_app
    : Z3_context * Z3_func_decl * Z3_ast vector -> Z3_ast

  val Z3_mk_const
    : Z3_context * Z3_symbol * Z3_sort -> Z3_ast

  val Z3_mk_fresh_func_decl
    : Z3_context * Z3_string * Z3_sort vector * Z3_sort -> Z3_func_decl

  val Z3_mk_fresh_const
    : Z3_context * Z3_string * Z3_sort -> Z3_ast

  structure Propositional : (* Z3_Propositional *)
  sig
    type Z3_context = Z3_context
    type Z3_ast     = Z3_ast

    val Z3_mk_true
      : Z3_context -> Z3_ast

    val Z3_mk_false
      : Z3_context -> Z3_ast

    val Z3_mk_eq
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_distinct
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_not
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_ite
      : Z3_context * Z3_ast * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_iff
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_implies
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_xor
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_and
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_or
      : Z3_context * Z3_ast vector -> Z3_ast

  end (* Propositional *)

  structure Arithmetic : (* Z3_Arithmetic *)
  sig
    type Z3_context = Z3_context
    type Z3_ast     = Z3_ast

    val Z3_mk_add
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_mul
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_sub
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_unary_minus
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_div
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_mod
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_rem
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_power
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_lt
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_le
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_gt
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_ge
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_int2real
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_real2int
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_is_int
      : Z3_context * Z3_ast -> Z3_ast

  end (* Arithmetic *)

  structure BitVector : (* Z3_BitVector *)
  sig
    type Z3_context = Z3_context
    type Z3_ast     = Z3_ast
    type Z3_bool    = Z3_bool

    val Z3_mk_bvnot
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_bvredand
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_bvredor
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_bvand
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvor
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvxor
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvnand
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvnor
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvxnor
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvneg
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_bvadd
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsub
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvmul
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvudiv
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsdiv
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvurem
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsrem
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsmod
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvult
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvslt
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvule
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsle
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvuge
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsge
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvugt
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsgt
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_concat
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_extract
      : Z3_context * word * word * Z3_ast -> Z3_ast

    val Z3_mk_sign_ext
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_zero_ext
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_repeat
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_bvshl
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvlshr
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvashr
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_rotate_left
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_rotate_right
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_ext_rotate_left
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_ext_rotate_right
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_int2bv
      : Z3_context * word * Z3_ast -> Z3_ast

    val Z3_mk_bv2int
      : Z3_context * Z3_ast * Z3_bool -> Z3_ast

    val Z3_mk_bvadd_no_overflow
      : Z3_context * Z3_ast * Z3_ast * Z3_bool -> Z3_ast

    val Z3_mk_bvadd_no_underflow
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsub_no_overflow
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvsub_no_underflow
      : Z3_context * Z3_ast * Z3_ast * Z3_bool -> Z3_ast

    val Z3_mk_bvsdiv_no_overflow
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_bvneg_no_overflow
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_bvmul_no_overflow
      : Z3_context * Z3_ast * Z3_ast * Z3_bool -> Z3_ast

    val Z3_mk_bvmul_no_underflow
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

  end (* BitVector *)

  structure Array : (* Z3_Array *)
  sig
    type Z3_context   = Z3_context
    type Z3_ast       = Z3_ast
    type Z3_sort      = Z3_sort
    type Z3_func_decl = Z3_func_decl

    val Z3_mk_select
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_store
      : Z3_context * Z3_ast * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_const_array
      : Z3_context * Z3_sort * Z3_ast -> Z3_ast

    val Z3_mk_map
      : Z3_context * Z3_func_decl * Z3_ast vector -> Z3_ast

    val Z3_mk_array_default
      : Z3_context * Z3_ast -> Z3_ast
  end

  structure Set : (* Z3_Set *)
  sig
    type Z3_context = Z3_context
    type Z3_sort    = Z3_sort
    type Z3_ast     = Z3_ast

    val Z3_mk_set_sort
      : Z3_context * Z3_sort -> Z3_sort

    val Z3_mk_empty_set
      : Z3_context * Z3_sort -> Z3_ast

    val Z3_mk_full_set
      : Z3_context * Z3_sort -> Z3_ast

    val Z3_mk_set_add
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_set_del
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_set_union
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_set_intersect
      : Z3_context * Z3_ast vector -> Z3_ast

    val Z3_mk_set_difference
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_set_complement
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_set_member
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast

    val Z3_mk_set_subset
      : Z3_context * Z3_ast * Z3_ast -> Z3_ast
  end (* Set *)

  structure Numerals :
  sig
    type Z3_context = Z3_context
    type Z3_string  = Z3_string
    type Z3_sort    = Z3_sort
    type Z3_ast     = Z3_ast

    val Z3_mk_numeral
      : Z3_context * Z3_string * Z3_sort -> Z3_ast

    val Z3_mk_real
      : Z3_context * int * int -> Z3_ast

    val Z3_mk_int
      : Z3_context * int * Z3_sort -> Z3_ast

    val Z3_mk_unsigned_int
      : Z3_context * word * Z3_sort -> Z3_ast
  end (* Numerals *)

  structure Quantifier : (* Z3_Quantifier *)
  sig
    type Z3_context = Z3_context
    type Z3_pattern = Z3_pattern
    type Z3_sort    = Z3_sort
    type Z3_ast     = Z3_ast
    type Z3_app     = Z3_app
    type Z3_symbol  = Z3_symbol
    type Z3_bool    = Z3_bool

    val Z3_mk_pattern
      : Z3_context * Z3_ast vector -> Z3_pattern

    val Z3_mk_bound
      : Z3_context * word * Z3_sort -> Z3_ast

    val Z3_mk_forall
      : Z3_context * word
                   * Z3_pattern vector
                   * Z3_sort vector * Z3_symbol vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_exists
      : Z3_context * word
                   * Z3_pattern vector
                   * Z3_sort vector * Z3_symbol vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_quantifier
      : Z3_context * Z3_bool * word
                   * Z3_pattern vector
                   * Z3_sort vector * Z3_symbol vector
                  * Z3_ast -> Z3_ast

    val Z3_mk_quantifier_ex
      : Z3_context * Z3_bool * word
                   * Z3_symbol * Z3_symbol
                   * Z3_pattern vector
                   * Z3_ast vector
                   * Z3_sort vector * Z3_symbol vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_forall_const
      : Z3_context * word
                   * Z3_app vector
                   * Z3_pattern vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_exists_const
      : Z3_context * word
                   * Z3_app vector
                   * Z3_pattern vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_quantifier_const
      : Z3_context * Z3_bool * word
                   * Z3_app vector
                   * Z3_pattern vector
                   * Z3_ast -> Z3_ast

    val Z3_mk_quantifier_const_ex
      : Z3_context * Z3_bool * word * Z3_symbol
                   * Z3_symbol
                   * Z3_app vector
                   * Z3_pattern vector
                   * Z3_ast vector
                   * Z3_ast -> Z3_ast

  end (* Quantifier *)

  structure Accessor : (* Z3_Accessor *)
  sig
    type Z3_context      = Z3_context
    type Z3_symbol       = Z3_symbol
    type Z3_sort         = Z3_sort
    type Z3_ast          = Z3_ast
    type Z3_func_decl    = Z3_func_decl
    type Z3_app          = Z3_app
    type Z3_pattern      = Z3_pattern
    type Z3_param_descrs = Z3_param_descrs
    type Z3_params       = Z3_params

    type Z3_string       = Z3_string

    type Z3_bool           = Z3_bool

    val Z3_get_symbol_kind
      : Z3_context * Z3_symbol -> Enum.Z3_symbol_kind.t

    val Z3_get_symbol_int
      : Z3_context * Z3_symbol -> int

    val Z3_get_symbol_string
       : Z3_context * Z3_symbol -> Z3_string

    val Z3_get_sort_name
      : Z3_context * Z3_sort -> Z3_symbol

    val Z3_get_sort_id
      : Z3_context * Z3_sort -> word

    val Z3_sort_to_ast
      : Z3_context * Z3_sort -> Z3_ast

    val Z3_is_eq_sort
      : Z3_context * Z3_sort * Z3_sort -> Z3_bool

    val Z3_get_sort_kind
      : Z3_context * Z3_sort -> Enum.Z3_sort_kind.t

    val Z3_get_bv_sort_size
      : Z3_context * Z3_sort -> word

    val Z3_get_array_sort_domain
      : Z3_context * Z3_sort -> Z3_sort

    val Z3_get_array_sort_range
      : Z3_context * Z3_sort -> Z3_sort

    val Z3_get_tuple_sort_mk_decl
      : Z3_context * Z3_sort -> Z3_func_decl

    val Z3_get_tuple_sort_num_fields
      : Z3_context * Z3_sort -> word

    val Z3_get_tuple_sort_field_decl
      : Z3_context * Z3_sort * word -> Z3_func_decl

    val Z3_get_datatype_sort_num_constructors
      : Z3_context * Z3_sort -> word

    val Z3_get_datatype_sort_constructor
      : Z3_context * Z3_sort * word -> Z3_func_decl

    val Z3_get_datatype_sort_recognizer
      : Z3_context * Z3_sort * word -> Z3_func_decl

    val Z3_get_datatype_sort_constructor_accessor
      : Z3_context * Z3_sort * word * word -> Z3_func_decl

    val Z3_get_relation_arity
      : Z3_context * Z3_sort -> word

    val Z3_get_relation_column
      : Z3_context * Z3_sort * word -> Z3_sort

    val Z3_func_decl_to_ast
      : Z3_context * Z3_func_decl -> Z3_ast

    val Z3_is_eq_func_decl
      : Z3_context * Z3_func_decl * Z3_func_decl -> Z3_bool

    val Z3_get_func_decl_id
      : Z3_context * Z3_func_decl -> word

    val Z3_get_decl_name
      : Z3_context * Z3_func_decl -> Z3_symbol

    val Z3_get_decl_kind
      : Z3_context * Z3_func_decl -> Enum.Z3_decl_kind.t

    val Z3_get_domain_size
      : Z3_context * Z3_func_decl -> word

    val Z3_get_arity
      : Z3_context * Z3_func_decl -> word

    val Z3_get_domain
      : Z3_context * Z3_func_decl * word -> Z3_sort

    val Z3_get_range
      : Z3_context * Z3_func_decl -> Z3_sort

    val Z3_get_decl_num_parameters
      : Z3_context * Z3_func_decl -> word

    val Z3_get_decl_parameter_kind
      : Z3_context * Z3_func_decl * word -> Enum.Z3_parameter_kind.t

    val Z3_get_decl_int_parameter
      : Z3_context * Z3_func_decl * word -> int

    val Z3_get_decl_double_parameter
      : Z3_context * Z3_func_decl * word -> real

    val Z3_get_decl_symbol_parameter
      : Z3_context * Z3_func_decl * word -> Z3_symbol

    val Z3_get_decl_sort_parameter
      : Z3_context * Z3_func_decl * word -> Z3_sort

    val Z3_get_decl_ast_parameter
      : Z3_context * Z3_func_decl * word -> Z3_ast

    val Z3_get_decl_func_decl_parameter
      : Z3_context * Z3_func_decl * word -> Z3_func_decl

    val Z3_get_decl_rational_parameter
       : Z3_context * Z3_func_decl * word -> Z3_string

    val Z3_app_to_ast
      : Z3_context * Z3_app -> Z3_ast

    val Z3_get_app_decl
      : Z3_context * Z3_app -> Z3_func_decl

    val Z3_get_app_num_args
      : Z3_context * Z3_app -> word

    val Z3_get_app_arg
      : Z3_context * Z3_app * word -> Z3_ast

    val Z3_is_eq_ast
      : Z3_context * Z3_ast * Z3_ast -> Z3_bool

    val Z3_get_ast_id
      : Z3_context * Z3_ast -> word

    val Z3_get_ast_hash
      : Z3_context * Z3_ast -> word

    val Z3_get_sort
      : Z3_context * Z3_ast -> Z3_sort

    val Z3_is_well_sorted
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_get_bool_value
      : Z3_context * Z3_ast -> Enum.Z3_lbool.t

    val Z3_get_ast_kind
      : Z3_context * Z3_ast -> Enum.Z3_ast_kind.t

    val Z3_is_app
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_is_numeral_ast
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_is_algebraic_number
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_to_app
      : Z3_context * Z3_ast -> Z3_app

    val Z3_to_func_decl
      : Z3_context * Z3_ast -> Z3_func_decl

    val Z3_get_numeral_string
       : Z3_context * Z3_ast -> Z3_string

    val Z3_get_numeral_decimal_string
       : Z3_context * Z3_ast * word -> Z3_string

    val Z3_get_numerator
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_get_denominator
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_get_numeral_int
      : Z3_context * Z3_ast * int ref -> Z3_bool

    val Z3_get_numeral_uint
      : Z3_context * Z3_ast * word ref -> Z3_bool

    val Z3_get_algebraic_number_lower
      : Z3_context * Z3_ast * word -> Z3_ast

    val Z3_get_algebraic_number_upper
      : Z3_context * Z3_ast * word -> Z3_ast

    val Z3_pattern_to_ast
      : Z3_context * Z3_pattern -> Z3_ast

    val Z3_get_pattern_num_terms
      : Z3_context * Z3_pattern -> word

    val Z3_get_pattern
      : Z3_context * Z3_pattern * word -> Z3_ast

    val Z3_get_index_value
      : Z3_context * Z3_ast -> word

    val Z3_is_quantifier_forall
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_get_quantifier_weight
      : Z3_context * Z3_ast -> word

    val Z3_get_quantifier_num_patterns
      : Z3_context * Z3_ast -> word

    val Z3_get_quantifier_pattern_ast
      : Z3_context * Z3_ast * word -> Z3_pattern

    val Z3_get_quantifier_num_no_patterns
      : Z3_context * Z3_ast -> word

    val Z3_get_quantifier_no_pattern_ast
      : Z3_context * Z3_ast * word -> Z3_ast

    val Z3_get_quantifier_num_bound
      : Z3_context * Z3_ast -> word

    val Z3_get_quantifier_bound_name
      : Z3_context * Z3_ast * word -> Z3_symbol

    val Z3_get_quantifier_bound_sort
      : Z3_context * Z3_ast * word -> Z3_sort

    val Z3_get_quantifier_body
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_simplify
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_simplify_ex
      : Z3_context * Z3_ast * Z3_params -> Z3_ast

    val Z3_simplify_get_help
       : Z3_context -> Z3_string

    val Z3_simplify_get_param_descrs
      : Z3_context -> Z3_param_descrs

  end (* Accessor *)

  val Z3_update_term
    : Z3_context * Z3_ast * Z3_ast vector -> Z3_ast

  val Z3_substitute
    : Z3_context * Z3_ast * Z3_ast vector * Z3_ast vector -> Z3_ast

  val Z3_substitute_vars
    : Z3_context * Z3_ast * Z3_ast vector -> Z3_ast

  val Z3_translate
    : Z3_context * Z3_ast * Z3_contextarget -> Z3_ast

  structure Model : (* Z3_Models *)
  sig
    type Z3_context     = Z3_context
    type Z3_model       = Z3_model
    type Z3_ast         = Z3_ast
    type Z3_func_decl   = Z3_func_decl
    type Z3_func_interp = Z3_func_interp
    type Z3_sort        = Z3_sort
    type Z3_func_entry  = Z3_func_entry
    type Z3_bool        = Z3_bool

    val Z3_model_inc_ref
      : Z3_context * Z3_model -> unit

    val Z3_model_dec_ref
      : Z3_context * Z3_model -> unit

    val Z3_model_eval
      : Z3_context * Z3_model * Z3_ast * Z3_bool * Z3_ast ref -> Z3_bool

    val Z3_model_get_const_interp
      : Z3_context * Z3_model * Z3_func_decl -> Z3_ast

    val Z3_model_get_func_interp
      : Z3_context * Z3_model * Z3_func_decl -> Z3_func_interp

    val Z3_model_get_num_consts
      : Z3_context * Z3_model -> word

    val Z3_model_get_const_decl
      : Z3_context * Z3_model * word -> Z3_func_decl

    val Z3_model_get_num_funcs
      : Z3_context * Z3_model -> word

    val Z3_model_get_func_decl
      : Z3_context * Z3_model * word -> Z3_func_decl

    val Z3_model_get_num_sorts
      : Z3_context * Z3_model -> word

    val Z3_model_get_sort
      : Z3_context * Z3_model * word -> Z3_sort

    val Z3_model_get_sort_universe
      : Z3_context * Z3_model * Z3_sort -> Z3_ast_vector

    val Z3_is_as_array
      : Z3_context * Z3_ast -> Z3_bool

    val Z3_get_as_array_func_decl
      : Z3_context * Z3_ast -> Z3_func_decl

    val Z3_func_interp_inc_ref
      : Z3_context * Z3_func_interp -> unit

    val Z3_func_interp_dec_ref
      : Z3_context * Z3_func_interp -> unit

    val Z3_func_interp_get_num_entries
      : Z3_context * Z3_func_interp -> word

    val Z3_func_interp_get_entry
      : Z3_context * Z3_func_interp * word -> Z3_func_entry

    val Z3_func_interp_get_else
      : Z3_context * Z3_func_interp -> Z3_ast

    val Z3_func_interp_get_arity
      : Z3_context * Z3_func_interp -> word

    val Z3_func_entry_inc_ref
      : Z3_context * Z3_func_entry -> unit

    val Z3_func_entry_dec_ref
      : Z3_context * Z3_func_entry -> unit

    val Z3_func_entry_get_value
      : Z3_context * Z3_func_entry -> Z3_ast

    val Z3_func_entry_get_num_args
      : Z3_context * Z3_func_entry -> word

    val Z3_func_entry_get_arg
      : Z3_context * Z3_func_entry * word -> Z3_ast

  end

  structure Log : (* Z3_Log *)
  sig
    type Z3_string = Z3_string
    type Z3_bool   = Z3_bool

    val Z3_open_log
      : Z3_string -> Z3_bool

    val Z3_append_log
      : Z3_string -> unit

    val Z3_close_log
      : unit -> unit

    val Z3_toggle_warning_messages
      : Z3_bool -> unit
  end (* Log *)

  structure Stringconv : (* Z3_Stringconv *)
  sig
    type Z3_context        = Z3_context
    type Z3_ast            = Z3_ast
    type Z3_string         = Z3_string
    type Z3_pattern        = Z3_pattern
    type Z3_model          = Z3_model
    type Z3_func_decl      = Z3_func_decl
    type Z3_sort           = Z3_sort

    val Z3_set_ast_print_mode
      : Z3_context * Enum.Z3_ast_print_mode.t -> unit

    val Z3_ast_to_string
       : Z3_context * Z3_ast -> Z3_string

    val Z3_pattern_to_string
       : Z3_context * Z3_pattern -> Z3_string

    val Z3_sort_to_string
       : Z3_context * Z3_sort -> Z3_string

    val Z3_func_decl_to_string
       : Z3_context * Z3_func_decl -> Z3_string

    val Z3_model_to_string
       : Z3_context * Z3_model -> Z3_string

    val Z3_benchmark_to_smtlib_string
       : Z3_context * Z3_string * Z3_string
                    * Z3_string * Z3_string
                    * Z3_ast vector * Z3_ast
                    -> Z3_string

  end (* Stringconv *)

  structure Parser : (* Z3_Parser *)
  sig
    type Z3_symbol    = Z3_symbol
    type Z3_ast       = Z3_ast
    type Z3_context   = Z3_context
    type Z3_sort      = Z3_sort
    type Z3_func_decl = Z3_func_decl
    type Z3_string    = Z3_string

    val Z3_parse_smtlib2_string
      : Z3_context * Z3_string
                   * Z3_symbol vector * Z3_sort vector
                   * Z3_symbol vector * Z3_func_decl vector
				   -> Z3_ast

    val Z3_parse_smtlib2_file
      : Z3_context * Z3_string
                   * Z3_symbol vector * Z3_sort vector
                   * Z3_symbol vector * Z3_func_decl vector
				   -> Z3_ast

    val Z3_parse_smtlib_string
      : Z3_context * Z3_string
                   * Z3_symbol vector * Z3_sort vector
                   * Z3_symbol vector * Z3_func_decl vector
				   -> unit

    val Z3_parse_smtlib_file
      : Z3_context * Z3_string
                   * Z3_symbol vector * Z3_sort vector
                   * Z3_symbol vector * Z3_func_decl vector
				   -> unit

    val Z3_get_smtlib_num_formulas
      : Z3_context -> word

    val Z3_get_smtlib_formula
      : Z3_context * word -> Z3_ast

    val Z3_get_smtlib_num_assumptions
      : Z3_context -> word

    val Z3_get_smtlib_assumption
      : Z3_context * word -> Z3_ast

    val Z3_get_smtlib_num_decls
      : Z3_context -> word

    val Z3_get_smtlib_decl
      : Z3_context * word -> Z3_func_decl

    val Z3_get_smtlib_num_sorts
      : Z3_context -> word

    val Z3_get_smtlib_sort
      : Z3_context * word -> Z3_sort

     val Z3_get_smtlib_error
        : Z3_context -> Z3_string

  end (* Parser *)

  structure Error : (* Z3_Error *)
  sig
    type Z3_context       = Z3_context
    type Z3_error_handler = Z3_error_handler
    type Z3_string        = Z3_string

    val Z3_get_error_code
      : Z3_context -> Enum.Z3_error_code.t

    val Z3_set_error_handler
      : Z3_context * Z3_error_handler option -> unit

    val Z3_set_error
      : Z3_context * Enum.Z3_error_code.t -> unit

    val Z3_get_error_msg_ex
      : Z3_context * Enum.Z3_error_code.t -> Z3_string
  end (* Error *)

  val Z3_get_version
    : word ref * word ref * word ref * word ref -> unit

  val Z3_enable_trace
    : Z3_string -> unit

  val Z3_disable_trace
    : Z3_string -> unit

  val Z3_reset_memory
    : unit -> unit

  structure ExternalTheoryPlugin : (* Z3_ExternalTheoryPlugin *)
  sig
    type Z3_context     = Z3_context
    type Z3_theory      = Z3_theory
    type Z3_theory_data = Z3_theory_data
    type Z3_symbol      = Z3_symbol
    type Z3_sort        = Z3_sort
    type Z3_ast         = Z3_ast
    type Z3_func_decl   = Z3_func_decl

    type Z3_string = Z3_string
    type Z3_bool   = Z3_bool

    type Z3_reduce_app_callback_fptr      = Z3_reduce_app_callback_fptr
    type Z3_reduce_eq_callback_fptr       = Z3_reduce_eq_callback_fptr
    type Z3_reduce_distinct_callback_fptr = Z3_reduce_distinct_callback_fptr

    val Z3_mk_theory
      : Z3_context * Z3_string * Z3_theory_data -> Z3_theory

    val Z3_theory_get_ext_data
      : Z3_theory -> Z3_theory_data

    val Z3_theory_mk_sort
      : Z3_context * Z3_theory * Z3_symbol -> Z3_sort

    val Z3_theory_mk_value
      : Z3_context * Z3_theory * Z3_symbol * Z3_sort -> Z3_ast

    val Z3_theory_mk_constant
      : Z3_context * Z3_theory * Z3_symbol * Z3_sort -> Z3_ast

    val Z3_theory_mk_func_decl
      : Z3_context * Z3_theory * Z3_symbol * Z3_sort vector * Z3_sort -> Z3_func_decl

    val Z3_theory_get_context
      : Z3_theory -> Z3_context

    val Z3_set_reduce_app_callback
      : Z3_theory * Z3_reduce_app_callback_fptr -> unit

    val Z3_set_reduce_eq_callback
      : Z3_theory * Z3_reduce_eq_callback_fptr -> unit

    val Z3_set_reduce_distinct_callback
      : Z3_theory * Z3_reduce_distinct_callback_fptr -> unit

    val Z3_set_delete_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_new_app_callback
      : Z3_theory * (Z3_theory * Z3_ast -> unit) -> unit

    val Z3_set_new_elem_callback
      : Z3_theory * (Z3_theory * Z3_ast -> unit) -> unit

    val Z3_set_init_search_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_push_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_pop_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_restart_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_reset_callback
      : Z3_theory * (Z3_theory -> unit) -> unit

    val Z3_set_final_check_callback
      : Z3_theory * (Z3_theory -> Z3_bool) -> unit

    val Z3_set_new_eq_callback
      : Z3_theory * (Z3_theory * Z3_ast * Z3_ast -> unit) -> unit

    val Z3_set_new_diseq_callback
      : Z3_theory * (Z3_theory * Z3_ast * Z3_ast -> unit) -> unit

    val Z3_set_new_assignment_callback
      : Z3_theory * (Z3_theory * Z3_ast * Z3_bool -> unit) -> unit

    val Z3_set_new_relevant_callback
      : Z3_theory * (Z3_theory * Z3_ast -> unit) -> unit

    val Z3_theory_assert_axiom
      : Z3_theory * Z3_ast -> unit

    val Z3_theory_assume_eq
      : Z3_theory * Z3_ast * Z3_ast -> unit

    val Z3_theory_enable_axiom_simplification
      : Z3_theory * Z3_bool -> unit

    val Z3_theory_get_eqc_root
      : Z3_theory * Z3_ast -> Z3_ast

    val Z3_theory_get_eqc_next
      : Z3_theory * Z3_ast -> Z3_ast

    val Z3_theory_get_num_parents
      : Z3_theory * Z3_ast -> word

    val Z3_theory_get_parent
      : Z3_theory * Z3_ast * word -> Z3_ast

    val Z3_theory_is_value
      : Z3_theory * Z3_ast -> Z3_bool

    val Z3_theory_is_decl
      : Z3_theory * Z3_func_decl -> Z3_bool

    val Z3_theory_get_num_elems
      : Z3_theory -> word

    val Z3_theory_get_elem
      : Z3_theory * word -> Z3_ast

    val Z3_theory_get_num_apps
      : Z3_theory -> word

    val Z3_theory_get_app
      : Z3_theory * word -> Z3_ast

  end (* ExternalTheoryPlugin *)

  structure Fixedpoint : (* Z3_Fixedpoint *)
  sig
    type Z3_fixedpoint   = Z3_fixedpoint
    type Z3_context      = Z3_context
    type Z3_symbol       = Z3_symbol
    type Z3_ast          = Z3_ast
    type Z3_func_decl    = Z3_func_decl
    type Z3_params       = Z3_params
    type Z3_param_descrs = Z3_param_descrs
    type Z3_ast_vector   = Z3_ast_vector
    type Z3_string       = Z3_string
    type Z3_stats        = Z3_stats

    type Z3_fixedpoint_reduce_assign_callback_fptr = Z3_fixedpoint_reduce_assign_callback_fptr
    type Z3_fixedpoint_reduce_app_callback_fptr    = Z3_fixedpoint_reduce_app_callback_fptr

    val Z3_mk_fixedpoint
      : Z3_context -> Z3_fixedpoint

    val Z3_fixedpoint_inc_ref
      : Z3_context * Z3_fixedpoint -> unit

    val Z3_fixedpoint_dec_ref
      : Z3_context * Z3_fixedpoint -> unit

    val Z3_fixedpoint_add_rule
      : Z3_context * Z3_fixedpoint * Z3_ast * Z3_symbol -> unit

    val Z3_fixedpoint_add_fact
      : Z3_context * Z3_fixedpoint * Z3_func_decl * word vector -> unit

    val Z3_fixedpoint_assert
      : Z3_context * Z3_fixedpoint * Z3_ast -> unit

    val Z3_fixedpoint_query
      : Z3_context * Z3_fixedpoint * Z3_ast -> Enum.Z3_lbool.t

    val Z3_fixedpoint_query_relations
      : Z3_context * Z3_fixedpoint * Z3_func_decl vector -> Enum.Z3_lbool.t

    val Z3_fixedpoint_get_answer
      : Z3_context * Z3_fixedpoint -> Z3_ast

    val Z3_fixedpoint_get_reason_unknown
       : Z3_context * Z3_fixedpoint -> Z3_string

    val Z3_fixedpoint_update_rule
      : Z3_context * Z3_fixedpoint * Z3_ast * Z3_symbol -> unit

    val Z3_fixedpoint_get_num_levels
      : Z3_context * Z3_fixedpoint * Z3_func_decl -> word

    val Z3_fixedpoint_get_cover_delta
      : Z3_context * Z3_fixedpoint * int * Z3_func_decl -> Z3_ast

    val Z3_fixedpoint_add_cover
      : Z3_context * Z3_fixedpoint * int * Z3_func_decl * Z3_ast -> unit

    val Z3_fixedpoint_get_statistics
      : Z3_context * Z3_fixedpoint -> Z3_stats

    val Z3_fixedpoint_register_relation
      : Z3_context * Z3_fixedpoint * Z3_func_decl -> unit

    val Z3_fixedpoint_set_predicate_representation
      : Z3_context * Z3_fixedpoint * Z3_func_decl * Z3_symbol vector -> unit

    val Z3_fixedpoint_get_rules
      : Z3_context * Z3_fixedpoint -> Z3_ast_vector

    val Z3_fixedpoint_get_assertions
      : Z3_context * Z3_fixedpoint -> Z3_ast_vector

    val Z3_fixedpoint_set_params
      : Z3_context * Z3_fixedpoint * Z3_params -> unit

    val Z3_fixedpoint_get_help
       : Z3_context * Z3_fixedpoint -> Z3_string

    val Z3_fixedpoint_get_param_descrs
      : Z3_context * Z3_fixedpoint -> Z3_param_descrs

    val Z3_fixedpoint_to_string
      : Z3_context * Z3_fixedpoint * Z3_ast vector -> Z3_string

    val Z3_fixedpoint_from_string
	  : Z3_context * Z3_fixedpoint * Z3_string -> Z3_ast_vector

	val Z3_fixedpoint_from_file
	  : Z3_context * Z3_fixedpoint * Z3_string -> Z3_ast_vector

    val Z3_fixedpoint_push
      : Z3_context * Z3_fixedpoint -> unit

    val Z3_fixedpoint_pop
      : Z3_context * Z3_fixedpoint -> unit

    val Z3_fixedpoint_init
      : Z3_context * Z3_fixedpoint * unit ptr -> unit

    val Z3_fixedpoint_set_reduce_assign_callback
      : Z3_context * Z3_fixedpoint * Z3_fixedpoint_reduce_assign_callback_fptr -> unit

    val Z3_fixedpoint_set_reduce_app_callback
      : Z3_context * Z3_fixedpoint * Z3_fixedpoint_reduce_app_callback_fptr -> unit

  end (* Fixedpoint *)

  structure AstVector : (* Z3_Ast_Vector *)
  sig
    type Z3_context    = Z3_context
    type Z3_ast        = Z3_ast
    type Z3_ast_vector = Z3_ast_vector
    type Z3_string     = Z3_string

    val Z3_mk_ast_vector
      : Z3_context -> Z3_ast_vector

    val Z3_ast_vector_inc_ref
      : Z3_context * Z3_ast_vector -> unit

    val Z3_ast_vector_dec_ref
      : Z3_context * Z3_ast_vector -> unit

    val Z3_ast_vector_size
      : Z3_context * Z3_ast_vector -> word

    val Z3_ast_vector_get
      : Z3_context * Z3_ast_vector * word -> Z3_ast

    val Z3_ast_vector_set
      : Z3_context * Z3_ast_vector * word * Z3_ast -> unit

    val Z3_ast_vector_resize
      : Z3_context * Z3_ast_vector * word -> unit

    val Z3_ast_vector_push
      : Z3_context * Z3_ast_vector * Z3_ast -> unit

    val Z3_ast_vector_translate
      : Z3_context * Z3_ast_vector * Z3_context -> Z3_ast_vector

    val Z3_ast_vector_to_string
      : Z3_context * Z3_ast_vector -> Z3_string

  end (* AstVector *)

  structure AstMap : (* Z3_Ast_Map *)
  sig
    type Z3_context    = Z3_context
    type Z3_ast        = Z3_ast
    type Z3_ast_vector = Z3_ast_vector
    type Z3_ast_map    = Z3_ast_map
    type Z3_string     = Z3_string
    type Z3_bool       = Z3_bool

    val Z3_mk_ast_map
      : Z3_context -> Z3_ast_map

    val Z3_ast_map_inc_ref
      : Z3_context * Z3_ast_map -> unit

    val Z3_ast_map_dec_ref
      : Z3_context * Z3_ast_map -> unit

    val Z3_ast_map_contains
      : Z3_context * Z3_ast_map * Z3_ast -> Z3_bool

    val Z3_ast_map_find
      : Z3_context * Z3_ast_map * Z3_ast -> Z3_ast

    val Z3_ast_map_insert
      : Z3_context * Z3_ast_map * Z3_ast * Z3_ast -> unit

    val Z3_ast_map_erase
      : Z3_context * Z3_ast_map * Z3_ast -> unit

    val Z3_ast_map_reset
      : Z3_context * Z3_ast_map -> unit

    val Z3_ast_map_size
      : Z3_context * Z3_ast_map -> word

    val Z3_ast_map_keys
      : Z3_context * Z3_ast_map -> Z3_ast_vector

    val Z3_ast_map_to_string
       : Z3_context * Z3_ast_map -> Z3_string

  end (* AstMap *)

  structure Goal : (* Z3_Goal *)
  sig
    type Z3_context   = Z3_context
    type Z3_goal      = Z3_goal
    type Z3_ast       = Z3_ast
    type Z3_bool      = Z3_bool
    type Z3_string    = Z3_string

    val Z3_mk_goal
      : Z3_context * Z3_bool * Z3_bool * Z3_bool -> Z3_goal

    val Z3_goal_inc_ref
      : Z3_context * Z3_goal -> unit

    val Z3_goal_dec_ref
      : Z3_context * Z3_goal -> unit

    val Z3_goal_precision
      : Z3_context * Z3_goal -> Enum.Z3_goal_prec.t

    val Z3_goal_assert
      : Z3_context * Z3_goal * Z3_ast -> unit

    val Z3_goal_inconsistent
      : Z3_context * Z3_goal -> Z3_bool

    val Z3_goal_depth
      : Z3_context * Z3_goal -> word

    val Z3_goal_reset
      : Z3_context * Z3_goal -> unit

    val Z3_goal_size
      : Z3_context * Z3_goal -> word

    val Z3_goal_formula
      : Z3_context * Z3_goal * word -> Z3_ast

    val Z3_goal_num_exprs
      : Z3_context * Z3_goal -> word

    val Z3_goal_is_decided_sat
      : Z3_context * Z3_goal -> Z3_bool

    val Z3_goal_is_decided_unsat
      : Z3_context * Z3_goal -> Z3_bool

    val Z3_goal_translate
      : Z3_context * Z3_goal * Z3_context -> Z3_goal

    val Z3_goal_to_string
      : Z3_context * Z3_goal -> Z3_string

  end (* Goal *)

  structure TacticAndProbe : (* Z3_Tactic_And_Probe *)
  sig
    type Z3_context      = Z3_context
    type Z3_tactic       = Z3_tactic
    type Z3_probe        = Z3_probe
    type Z3_goal         = Z3_goal
    type Z3_apply_result = Z3_apply_result
    type Z3_params       = Z3_params
    type Z3_model        = Z3_model
    type Z3_string       = Z3_string
    type Z3_param_descrs = Z3_param_descrs

    val Z3_mk_tactic
      : Z3_context * Z3_string -> Z3_tactic

    val Z3_tactic_inc_ref
      : Z3_context * Z3_tactic -> unit

    val Z3_tactic_dec_ref
      : Z3_context * Z3_tactic -> unit

    val Z3_mk_probe
      : Z3_context * Z3_string -> Z3_probe

    val Z3_probe_inc_ref
      : Z3_context * Z3_probe -> unit

    val Z3_probe_dec_ref
      : Z3_context * Z3_probe -> unit

    val Z3_tactic_and_then
      : Z3_context * Z3_tactic * Z3_tactic -> Z3_tactic

    val Z3_tactic_or_else
      : Z3_context * Z3_tactic * Z3_tactic -> Z3_tactic

    val Z3_tactic_par_or
      : Z3_context * Z3_tactic vector -> Z3_tactic

    val Z3_tactic_par_and_then
      : Z3_context * Z3_tactic * Z3_tactic -> Z3_tactic

    val Z3_tactic_try_for
      : Z3_context * Z3_tactic * word -> Z3_tactic

    val Z3_tactic_when
      : Z3_context * Z3_probe * Z3_tactic -> Z3_tactic

    val Z3_tactic_cond
      : Z3_context * Z3_probe * Z3_tactic * Z3_tactic -> Z3_tactic

    val Z3_tactic_repeat
      : Z3_context * Z3_tactic * word -> Z3_tactic

    val Z3_tactic_skip
      : Z3_context -> Z3_tactic

    val Z3_tactic_fail
      : Z3_context -> Z3_tactic

    val Z3_tactic_fail_if
      : Z3_context * Z3_probe -> Z3_tactic

    val Z3_tactic_fail_if_not_decided
      : Z3_context -> Z3_tactic

    val Z3_tactic_using_params
      : Z3_context * Z3_tactic * Z3_params -> Z3_tactic

    val Z3_probe_const
      : Z3_context * real -> Z3_probe

    val Z3_probe_lt
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_gt
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_le
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_ge
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_eq
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_and
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_or
      : Z3_context * Z3_probe * Z3_probe -> Z3_probe

    val Z3_probe_not
      : Z3_context * Z3_probe -> Z3_probe

    val Z3_get_num_tactics
      : Z3_context -> word

    val Z3_get_tactic_name
      : Z3_context * word -> Z3_string

    val Z3_get_num_probes
      : Z3_context -> word

    val Z3_get_probe_name
      : Z3_context * word -> Z3_string

    val Z3_tactic_get_help
      : Z3_context * Z3_tactic -> Z3_string

    val Z3_tactic_get_param_descrs
      : Z3_context * Z3_tactic -> Z3_param_descrs

    val Z3_tactic_get_descr
      : Z3_context * Z3_string -> Z3_string

    val Z3_probe_get_descr
      : Z3_context * Z3_string -> Z3_string

    val Z3_probe_apply
      : Z3_context * Z3_probe * Z3_goal -> real

    val Z3_tactic_apply
      : Z3_context * Z3_tactic * Z3_goal -> Z3_apply_result

    val Z3_tactic_apply_ex
      : Z3_context * Z3_tactic * Z3_goal * Z3_params -> Z3_apply_result

    val Z3_apply_result_inc_ref
      : Z3_context * Z3_apply_result -> unit

    val Z3_apply_result_dec_ref
      : Z3_context * Z3_apply_result -> unit

    val Z3_apply_result_to_string
      : Z3_context * Z3_apply_result -> Z3_string

    val Z3_apply_result_get_num_subgoals
      : Z3_context * Z3_apply_result -> word

    val Z3_apply_result_get_subgoal
      : Z3_context * Z3_apply_result * word -> Z3_goal

    val Z3_apply_result_convert_model
      : Z3_context * Z3_apply_result * word * Z3_model -> Z3_model

  end (* TacticAndProbe *)

  structure Solver : (* Z3_Solver *)
  sig
    type Z3_context      = Z3_context
    type Z3_solver       = Z3_solver
    type Z3_symbol       = Z3_symbol
    type Z3_tactic       = Z3_tactic
    type Z3_params       = Z3_params
    type Z3_param_descrs = Z3_param_descrs
    type Z3_model        = Z3_model
    type Z3_stats        = Z3_stats
    type Z3_ast          = Z3_ast
    type Z3_ast_vector   = Z3_ast_vector
    type Z3_string       = Z3_string

    val Z3_mk_solver
      : Z3_context -> Z3_solver

    val Z3_mk_simple_solver
      : Z3_context -> Z3_solver

    val Z3_mk_solver_for_logic
      : Z3_context * Z3_symbol -> Z3_solver

    val Z3_mk_solver_from_tactic
      : Z3_context * Z3_tactic -> Z3_solver

    val Z3_solver_get_help
      : Z3_context * Z3_solver -> Z3_string

    val Z3_solver_get_param_descrs
      : Z3_context * Z3_solver -> Z3_param_descrs

    val Z3_solver_set_params
      : Z3_context * Z3_solver * Z3_params -> unit

    val Z3_solver_inc_ref
      : Z3_context * Z3_solver -> unit

    val Z3_solver_dec_ref
      : Z3_context * Z3_solver -> unit

    val Z3_solver_push
      : Z3_context * Z3_solver -> unit

    val Z3_solver_pop
      : Z3_context * Z3_solver * word -> unit

    val Z3_solver_reset
      : Z3_context * Z3_solver -> unit

    val Z3_solver_get_num_scopes
      : Z3_context * Z3_solver -> word

    val Z3_solver_assert
      : Z3_context * Z3_solver * Z3_ast -> unit

    val Z3_solver_assert_and_track
      : Z3_context * Z3_solver * Z3_ast * Z3_ast -> unit

    val Z3_solver_get_assertions
      : Z3_context * Z3_solver -> Z3_ast_vector

    val Z3_solver_check
      : Z3_context * Z3_solver -> Enum.Z3_lbool.t

    val Z3_solver_check_assumptions
      : Z3_context * Z3_solver * Z3_ast vector -> Enum.Z3_lbool.t

    val Z3_solver_get_model
      : Z3_context * Z3_solver -> Z3_model

    val Z3_solver_get_proof
      : Z3_context * Z3_solver -> Z3_ast

    val Z3_solver_get_unsat_core
      : Z3_context * Z3_solver -> Z3_ast_vector

    val Z3_solver_get_reason_unknown
      : Z3_context * Z3_solver -> Z3_string

    val Z3_solver_get_statistics
      : Z3_context * Z3_solver -> Z3_stats

    val Z3_solver_to_string
      : Z3_context * Z3_solver -> Z3_string
  end (* Solver *)

  structure Statistics :
  sig
    type Z3_context = Z3_context
    type Z3_stats   = Z3_stats
    type Z3_string  = Z3_string
    type Z3_bool    = Z3_bool

    val Z3_stats_to_string
      : Z3_context * Z3_stats -> Z3_string

    val Z3_stats_inc_ref
      : Z3_context * Z3_stats -> unit

    val Z3_stats_dec_ref
      : Z3_context * Z3_stats -> unit

    val Z3_stats_size
      : Z3_context * Z3_stats -> word

    val Z3_stats_get_key
      : Z3_context * Z3_stats * word -> Z3_string

    val Z3_stats_is_uint
      : Z3_context * Z3_stats * word -> Z3_bool

    val Z3_stats_is_double
      : Z3_context * Z3_stats * word -> Z3_bool

    val Z3_stats_get_uint_value
      : Z3_context * Z3_stats * word -> word

    val Z3_stats_get_double_value
      : Z3_context * Z3_stats * word -> real
  end (* Statistics *)

  structure Interpolation :
  sig
    type Z3_ast        = Z3_ast
    type Z3_context    = Z3_context
    type Z3_string     = Z3_string
    type Z3_config     = Z3_config
    type Z3_params     = Z3_params
    type Z3_ast_vector = Z3_ast_vector
    type Z3_model      = Z3_model

    val Z3_mk_interpolant
      : Z3_context * Z3_ast -> Z3_ast

    val Z3_mk_interpolation_context
      : Z3_config -> Z3_config

    val Z3_get_interpolant
      : Z3_context * Z3_ast * Z3_ast * Z3_params -> Z3_ast_vector

    val Z3_compute_interpolant
      : Z3_context * Z3_ast * Z3_params
                * Z3_ast_vector ref * Z3_model ref -> Enum.Z3_lbool.t

    val Z3_interpolation_profile
      : Z3_context -> Z3_string

    val Z3_read_interpolation_problem
      : Z3_context * word ref * Z3_ast ref ptr
                   * word ref ptr * Z3_string
                   * Z3_string ref * word ref * Z3_ast ref ptr -> int

    val Z3_check_interpolant
      : Z3_context * Z3_ast array
                   * word array * Z3_ast array * Z3_string ref
                   * Z3_ast array -> int

    val Z3_write_interpolation_problem
      : Z3_context * Z3_ast array
                 * word array * Z3_string * Z3_ast array -> unit
  end (* Interpolation *)

  val Z3_polynomial_subresultants
    : Z3_context * Z3_ast * Z3_ast * Z3_ast -> Z3_ast_vector

  structure RealClosedField :
  sig
    type Z3_context = Z3_context
    type Z3_rcf_num = Z3_rcf_num

    val Z3_rcf_del
      : Z3_context * Z3_rcf_num -> unit

    val Z3_rcf_mk_rational
      : Z3_context * Z3_string -> Z3_rcf_num

    val Z3_rcf_mk_small_int
      : Z3_context * int -> Z3_rcf_num

    val Z3_rcf_mk_pi
      : Z3_context -> Z3_rcf_num

    val Z3_rcf_mk_e
      : Z3_context -> Z3_rcf_num

    val Z3_rcf_mk_infinitesimal
      : Z3_context -> Z3_rcf_num

    val Z3_rcf_mk_roots
      : Z3_context * Z3_rcf_num vector * Z3_rcf_num array -> word

    val Z3_rcf_add
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_sub
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_mul
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_div
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_neg
      : Z3_context * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_inv
      : Z3_context * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_power
      : Z3_context * Z3_rcf_num * word -> Z3_rcf_num

    val Z3_rcf_lt
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_gt
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_le
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_ge
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_eq
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_neq
      : Z3_context * Z3_rcf_num * Z3_rcf_num -> Z3_rcf_num

    val Z3_rcf_num_to_string
      : Z3_context * Z3_rcf_num * Z3_bool * Z3_bool -> Z3_string

    val Z3_rcf_num_to_decimal_string
      : Z3_context * Z3_rcf_num * word -> Z3_string

    val Z3_rcf_get_numerator_denominator
      : Z3_context * Z3_rcf_num * Z3_rcf_num ref * Z3_rcf_num ref -> unit
  end (* Z3_RealClosedField *)

  structure Deprecated :
  sig
    type Z3_context   = Z3_context
    type Z3_model     = Z3_model
    type Z3_ast       = Z3_ast
    type Z3_symbol    = Z3_symbol
    type Z3_sort      = Z3_sort
    type Z3_bool      = Z3_bool
    type Z3_string    = Z3_string
    type Z3_literals  = Z3_literals
    type Z3_func_decl = Z3_func_decl
    type Z3_solver    = Z3_solver

    (*
     * Deprecated Injective functions API
     *)
    val Z3_mk_injective_function
      : Z3_context * Z3_symbol * Z3_sort vector * Z3_sort -> Z3_func_decl

    (*
     * Deprecated Constraints API
     *)
    val Z3_set_logic
      : Z3_context * Z3_string -> Z3_bool

    val Z3_push
      : Z3_context -> unit

    val Z3_pop
      : Z3_context * word -> unit

    val Z3_get_num_scopes
      : Z3_context -> word

    val Z3_persist_ast
      : Z3_context * Z3_ast * word -> unit

    val Z3_assert_cnstr
      : Z3_context * Z3_ast -> unit

    val Z3_check_and_get_model
      : Z3_context * Z3_model ref -> Enum.Z3_lbool.t

    val Z3_check
      : Z3_context -> Enum.Z3_lbool.t

    val Z3_check_assumptions
      : Z3_context * Z3_ast vector * Z3_model ref
        * Z3_ast ref * word ref * Z3_ast array -> Enum.Z3_lbool.t

    val Z3_get_implied_equalities
      : Z3_context * Z3_solver
        * Z3_ast vector * word array -> Enum.Z3_lbool.t

    val Z3_del_model
      : Z3_context * Z3_model -> unit

    (*
     * Deprecated Search control API
     *)
    val Z3_soft_check_cancel
      : Z3_context -> unit

    val Z3_get_search_failure
      : Z3_context -> Enum.Z3_search_failure.t

    (*
     * Deprecated Labels API
     *)
    val Z3_mk_label
      : Z3_context * Z3_symbol * Z3_bool * Z3_ast -> Z3_ast

    val Z3_get_relevant_labels
      : Z3_context -> Z3_literals

    val Z3_get_relevant_literals
      : Z3_context -> Z3_literals

    val Z3_get_guessed_literals
      : Z3_context -> Z3_literals

    val Z3_del_literals
      : Z3_context * Z3_literals -> unit

    val Z3_get_num_literals
      : Z3_context * Z3_literals -> word

    val Z3_get_label_symbol
      : Z3_context * Z3_literals * word -> Z3_symbol

    val Z3_get_literal
      : Z3_context * Z3_literals * word -> Z3_ast

    val Z3_disable_literal
      : Z3_context * Z3_literals * word -> unit

    val Z3_block_literals
      : Z3_context * Z3_literals -> unit

    (*
     * Deprecated Model API
     *)
    val Z3_get_model_num_constants
      : Z3_context * Z3_model -> word

    val Z3_get_model_constant
      : Z3_context * Z3_model * word -> Z3_func_decl

    val Z3_get_model_num_funcs
      : Z3_context * Z3_model -> word

    val Z3_get_model_func_decl
      : Z3_context * Z3_model * word -> Z3_func_decl

    val Z3_eval_func_decl
      : Z3_context * Z3_model * Z3_func_decl * Z3_ast ref -> Z3_bool

    val Z3_is_array_value
      : Z3_context * Z3_model * Z3_ast * word ref -> Z3_bool

    val Z3_get_array_value
      : Z3_context * Z3_model * Z3_ast * word
        * Z3_ast array * Z3_ast array * Z3_ast ref -> unit

    val Z3_get_model_func_else
      : Z3_context * Z3_model * word -> Z3_ast

    val Z3_get_model_func_num_entries
      : Z3_context * Z3_model * word -> word

    val Z3_get_model_func_entry_num_args
      : Z3_context * Z3_model * word * word -> word

    val Z3_get_model_func_entry_arg
      : Z3_context * Z3_model * word * word * word -> Z3_ast

    val Z3_get_model_func_entry_value
      : Z3_context * Z3_model * word * word -> Z3_ast

    val Z3_eval
      : Z3_context * Z3_model * Z3_ast * Z3_ast ref -> Z3_bool

    val Z3_eval_decl
      : Z3_context * Z3_model * Z3_func_decl
         * Z3_ast vector * Z3_ast ref -> Z3_bool

    (*
     * Deprecated String conversion API
     *)
    val Z3_context_to_string
      : Z3_context -> Z3_string

    val Z3_statistics_to_string
      : Z3_context -> Z3_string

    val Z3_get_context_assignment
      : Z3_context -> Z3_ast

    (*
     * Deprecated Error Handling API
     *)
    val Z3_get_error_msg
      : Enum.Z3_error_code.t -> Z3_string

  end (* Deprecated *)
end

