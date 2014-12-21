
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
  val libz3 = Library.libz3
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
  type Z3_rcf_num      = unit ptr
  type Z3_literals     = unit ptr
  type Z3_goal         = unit ptr

  type Z3_context          = unit ptr
  type Z3_sort_opt         = unit ptr
  type Z3_constructor      = unit ptr
  type Z3_constructor_list = unit ptr
  type Z3_string           = string
  type Z3_string_ptr       = Z3_string ref
  type Z3_param_descrs     = unit ptr
  type Z3_contextarget     = unit ptr
  type Z3_theory           = unit ptr
  type Z3_theory_data      = unit ptr

  type Z3_error_handler = Z3_context * Z3_enum.Z3_error_code -> unit

  type Z3_bool             = int
  val Z3_TRUE  : Z3_bool   = 1
  val Z3_FALSE : Z3_bool   = 0

  (**
   * Z3 enum constants
   *)
  structure Enum = Z3_enum

  (**
   * Algebraic Numbers
   *)
  structure Algebraic = Z3_Algebraic

  (**
   * Global configuration
   *)
  structure Global = Z3_Global

  (**
   * Config
   *)
  structure Config = Z3_Config

  (**
   * Context
   *)
  structure Context = Z3_Context

  (**
   * Parameters
   *)
  structure Parameter = Z3_Parameter

  (**
   *  Parameter Descriptions
   *)
  structure ParameterDesc = Z3_ParameterDesc

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
  structure Sort = Z3_Sort

  (**
   * Constans and Applications
   *)
  val Z3_mk_func_decl =
    Dyn.dlsym (libz3, "Z3_mk_func_decl")
    : _import (Z3_context, Z3_symbol, word, Z3_sort vector, Z3_sort) -> Z3_func_decl

  val Z3_mk_app =
    Dyn.dlsym (libz3, "Z3_mk_app")
    : _import (Z3_context, Z3_func_decl, word, Z3_ast vector) -> Z3_ast

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
  structure Propositional = Z3_Propositional

  (**
   * Arithmetic: Integers and Reals
   *)
  structure Arithmetic = Z3_Arithmetic

  (**
   * Bit-vectors
   *)
  structure BitVector = Z3_BitVector

  (**
   * Arrays
   *)
  structure Array = Z3_Array

  (**
   * Sets
   *)
  structure Set = Z3_Set

  (**
   * Numerals
   *)
  structure Numerals = Z3_Numerals

  (**
   * Quantifiers
   *)
  structure Quantifier = Z3_Quantifier

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
  structure Log = Z3_Log

  (**
   * String conversion
   *)
  structure Stringconv = Z3_Stringconv

  (**
   * Parser interface
   *)
  structure Parser = Z3_Parser

  (**
   * Error Handling
   *)
  structure Error = Z3_Error

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
   * Statistics
   *)
  structure Interpolation = Z3_Interpolation

  (**
   * Polynominal
   *)
  val Z3_polynomial_subresultants =
    Dyn.dlsym(libz3, "Z3_polynomial_subresultants")
    : _import (Z3_context, Z3_ast, Z3_ast, Z3_ast) -> Z3_ast_vector

  (**
   * Real Closed Fields API
   *)
  structure RealClosedField = Z3_RealClosedField

  (**
   * Deprecxated API
   *)
  structure Deprecated = Z3_Deprecated

end (* local *)
end

