
(*
 * Z3 wrapper structure to SML# 2.0.0
 * 
 * ref. http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html
 *)
structure Z3 : Z3 =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  structure Tag =
  struct
    type Z3_config           = unit
    type Z3_symbol           = unit
    type Z3_ast              = unit
    type Z3_sort             = unit
    type Z3_func_decl        = unit
    type Z3_app              = unit
    type Z3_pattern          = unit
    type Z3_params           = unit
    type Z3_model            = unit
    type Z3_func_interp      = unit
    type Z3_func_entry       = unit
    type Z3_fixedpoint       = unit
    type Z3_ast_vector       = unit
    type Z3_ast_map          = unit
    type Z3_tactic           = unit
    type Z3_probe            = unit
    type Z3_apply_result     = unit
    type Z3_solver           = unit
    type Z3_stats            = unit
    type Z3_rcf_num          = unit
    type Z3_literals         = unit
    type Z3_goal             = unit
    type Z3_context          = unit
    type Z3_constructor      = unit
    type Z3_constructor_list = unit
    type Z3_param_descrs     = unit
    type Z3_contextarget     = unit
    type Z3_theory           = unit
    type Z3_theory_data      = unit
  end

  type Z3_config           = Tag.Z3_config ptr
  type Z3_symbol           = Tag.Z3_symbol ptr
  type Z3_ast              = Tag.Z3_ast ptr
  type Z3_sort             = Tag.Z3_sort ptr
  type Z3_func_decl        = Tag.Z3_func_decl ptr
  type Z3_app              = Tag.Z3_app ptr
  type Z3_pattern          = Tag.Z3_pattern ptr
  type Z3_params           = Tag.Z3_params ptr
  type Z3_model            = Tag.Z3_model ptr
  type Z3_func_interp      = Tag.Z3_func_interp ptr
  type Z3_func_entry       = Tag.Z3_func_entry ptr
  type Z3_fixedpoint       = Tag.Z3_fixedpoint ptr
  type Z3_ast_vector       = Tag.Z3_ast_vector ptr
  type Z3_ast_map          = Tag.Z3_ast_map ptr
  type Z3_tactic           = Tag.Z3_tactic ptr
  type Z3_probe            = Tag.Z3_probe ptr
  type Z3_apply_result     = Tag.Z3_apply_result ptr
  type Z3_solver           = Tag.Z3_solver ptr
  type Z3_stats            = Tag.Z3_stats ptr
  type Z3_rcf_num          = Tag.Z3_rcf_num ptr
  type Z3_literals         = Tag.Z3_literals ptr
  type Z3_goal             = Tag.Z3_goal ptr
  type Z3_context          = Tag.Z3_context ptr
  type Z3_constructor      = Tag.Z3_constructor ptr
  type Z3_constructor_list = Tag.Z3_constructor_list ptr
  type Z3_param_descrs     = Tag.Z3_param_descrs ptr
  type Z3_contextarget     = Tag.Z3_contextarget ptr
  type Z3_theory           = Tag.Z3_theory ptr
  type Z3_theory_data      = Tag.Z3_theory_data ptr

  type Z3_string           = string
  type Z3_sort_opt         = Z3_sort option
  type Z3_string_ptr       = Z3_string ref

  datatype Z3_bool = datatype Z3_bool.t
  val Z3_TRUE  = Z3_bool.Z3_TRUE 
  val Z3_FALSE = Z3_bool.Z3_FALSE

  (**
   * Z3 enum constants
   *)
  structure Enum = Z3_enum

  type Z3_error_handler = Z3_context * Enum.Z3_error_code.t -> unit

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

  (**
   * Algebraic Numbers
   *)
  open Z3_Algebraic

  (**
   * Global configuration
   *)
  open Z3_Global

  (**
   * Config
   *)
  open Z3_Config

  (**
   * Context
   *)
  open Z3_Context

  (**
   * Parameters
   *)
  open Z3_Parameter

  (**
   *  Parameter Descriptions
   *)
  open Z3_ParameterDesc

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
  open Z3_Sort

  (**
   * Constans and Applications
   *)
  fun Z3_mk_func_decl (c, s, domain, range) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_func_decl"))
    ( c : Z3_context
    , s : Z3_symbol
    , Vector.length domain : int
    , domain : Z3_sort vector
    , range : Z3_sort) : Z3_func_decl

  fun Z3_mk_app (c, d, args) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_app"))
    ( c : Z3_context
    , d : Z3_func_decl
    , Vector.length args : int
    , args : Z3_ast vector) : Z3_ast

  val Z3_mk_const =
    Dyn.dlsym (libz3, "Z3_mk_const")
    : _import (Z3_context, Z3_symbol, Z3_sort) -> Z3_ast

  fun Z3_mk_fresh_func_decl (c, prefix, domain, range) =
    _ffiapply (Dyn.dlsym (libz3, "Z3_mk_fresh_func_decl"))
    ( c : Z3_context
    , prefix : Z3_string
    , Vector.length domain : int
    , domain : Z3_sort vector
    , range : Z3_sort) : Z3_func_decl

  val Z3_mk_fresh_const =
    Dyn.dlsym (libz3, "Z3_mk_fresh_const")
    : _import (Z3_context, Z3_string, Z3_sort) -> Z3_ast

  (**
   * Propositional Logic and Equality
   *)
  open Z3_Propositional

  (**
   * Arithmetic: Integers and Reals
   *)
  open Z3_Arithmetic

  (**
   * Bit-vectors
   *)
  open Z3_BitVector

  (**
   * Arrays
   *)
  open Z3_Array

  (**
   * Sets
   *)
  open Z3_Set

  (**
   * Numerals
   *)
  open Z3_Numerals

  (**
   * Quantifiers
   *)
  open Z3_Quantifier

  (**
   * Accessors
   *)
  open Z3_Accessor

  (**
   * Modifiers
   *)
  fun Z3_update_term (c, a, args) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_update_term"))
    ( c : Z3_context
    , a : Z3_ast
    , Vector.length args : int
    , args : Z3_ast vector) : Z3_ast

  fun Z3_substitute (c, a, from, to) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_substitute"))
    ( c : Z3_context
    , a : Z3_ast
    , Vector.length from : int
    , from : Z3_ast vector
    , to   : Z3_ast vector) : Z3_ast

  fun Z3_substitute_vars (c, a, to) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_substitute_vars"))
    ( c : Z3_context
    , a : Z3_ast
    , Vector.length to : int
    , to : Z3_ast vector) : Z3_ast

  val Z3_translate =
    Dyn.dlsym(libz3, "Z3_translate")
    : _import (Z3_context, Z3_ast, Z3_contextarget) -> Z3_ast

  (**
   * Models
   *)
  open Z3_Model

  (**
   * Interaction logging.
   *)
  open Z3_Log

  (**
   * String conversion
   *)
  open Z3_Stringconv

  (**
   * Parser interface
   *)
  open Z3_Parser

  (**
   * Error Handling
   *)
  open Z3_Error

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
  open Z3_ExternalTheoryPlugin

  (**
   * Fixpoint facilities
   *)
  open Z3_Fixedpoint

  (**
   * AST vectors
   *)
  open Z3_Ast_Vector

  (**
   * AST maps
   *)
  open Z3_Ast_Map

  (**
   * Goals
   *)
  open Z3_Goal

  (**
   * Tactics and Probes
   *)
  open Z3_Tactic_And_Probe

  (**
   * Solvers
   *)
  open Z3_Solver

  (**
   * Statistics
   *)
  open Z3_Statistics

  (**
   * Statistics
   *)
  open Z3_Interpolation

  (**
   * Polynominal
   *)
  val Z3_polynomial_subresultants =
    Dyn.dlsym(libz3, "Z3_polynomial_subresultants")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_ast) -> Z3_ast_vector

  (**
   * Real Closed Fields API
   *)
  open Z3_RealClosedField

  (**
   * Deprecated API
   *)
  structure Deprecated = Z3_Deprecated

end (* local *)
end

