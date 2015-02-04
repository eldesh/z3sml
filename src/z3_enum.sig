
signature Z3_ENUM =
sig
  eqtype Z3_lbool
  val Z3_L_FALSE : Z3_lbool
  val Z3_L_UNDEF : Z3_lbool
  val Z3_L_TRUE  : Z3_lbool

  eqtype Z3_symbol_kind
  val Z3_INT_SYMBOL    : Z3_symbol_kind
  val Z3_STRING_SYMBOL : Z3_symbol_kind

  eqtype Z3_parameter_kind
  val Z3_PARAMETER_INT       : Z3_parameter_kind
  val Z3_PARAMETER_DOUBLE    : Z3_parameter_kind
  val Z3_PARAMETER_RATIONAL  : Z3_parameter_kind
  val Z3_PARAMETER_SYMBOL    : Z3_parameter_kind
  val Z3_PARAMETER_SORT      : Z3_parameter_kind
  val Z3_PARAMETER_AST       : Z3_parameter_kind
  val Z3_PARAMETER_FUNC_DECL : Z3_parameter_kind

  eqtype Z3_sort_kind
  val Z3_UNINTERPRETED_SORT : Z3_sort_kind
  val Z3_BOOL_SORT          : Z3_sort_kind
  val Z3_INT_SORT           : Z3_sort_kind
  val Z3_REAL_SORT          : Z3_sort_kind
  val Z3_BV_SORT            : Z3_sort_kind
  val Z3_ARRAY_SORT         : Z3_sort_kind
  val Z3_DATATYPE_SORT      : Z3_sort_kind
  val Z3_RELATION_SORT      : Z3_sort_kind
  val Z3_FINITE_DOMAIN_SORT : Z3_sort_kind
  val Z3_UNKNOWN_SORT       : Z3_sort_kind

  eqtype Z3_ast_kind
  val Z3_NUMERAL_AST    : Z3_ast_kind
  val Z3_APP_AST        : Z3_ast_kind
  val Z3_VAR_AST        : Z3_ast_kind
  val Z3_QUANTIFIER_AST : Z3_ast_kind
  val Z3_SORT_AST       : Z3_ast_kind
  val Z3_FUNC_DECL_AST  : Z3_ast_kind
  val Z3_UNKNOWN_AST    : Z3_ast_kind

  eqtype Z3_decl_kind
  (* Basic *)
  val Z3_OP_TRUE     : Z3_decl_kind
  val Z3_OP_FALSE    : Z3_decl_kind
  val Z3_OP_EQ       : Z3_decl_kind
  val Z3_OP_DISTINCT : Z3_decl_kind
  val Z3_OP_ITE      : Z3_decl_kind
  val Z3_OP_AND      : Z3_decl_kind
  val Z3_OP_OR       : Z3_decl_kind
  val Z3_OP_IFF      : Z3_decl_kind
  val Z3_OP_XOR      : Z3_decl_kind
  val Z3_OP_NOT      : Z3_decl_kind
  val Z3_OP_IMPLIES  : Z3_decl_kind
  val Z3_OP_OEQ      : Z3_decl_kind
  (* Arithmetic *)
  val Z3_OP_ANUM    : Z3_decl_kind
  val Z3_OP_AGNUM   : Z3_decl_kind
  val Z3_OP_LE      : Z3_decl_kind
  val Z3_OP_GE      : Z3_decl_kind
  val Z3_OP_LT      : Z3_decl_kind
  val Z3_OP_GT      : Z3_decl_kind
  val Z3_OP_ADD     : Z3_decl_kind
  val Z3_OP_SUB     : Z3_decl_kind
  val Z3_OP_UMINUS  : Z3_decl_kind
  val Z3_OP_MUL     : Z3_decl_kind
  val Z3_OP_DIV     : Z3_decl_kind
  val Z3_OP_IDIV    : Z3_decl_kind
  val Z3_OP_REM     : Z3_decl_kind
  val Z3_OP_MOD     : Z3_decl_kind
  val Z3_OP_TO_REAL : Z3_decl_kind
  val Z3_OP_TO_INT  : Z3_decl_kind
  val Z3_OP_IS_INT  : Z3_decl_kind
  val Z3_OP_POWER   : Z3_decl_kind
  (* Arrays & Sets *)
  val Z3_OP_STORE          : Z3_decl_kind
  val Z3_OP_SELECT         : Z3_decl_kind
  val Z3_OP_CONST_ARRAY    : Z3_decl_kind
  val Z3_OP_ARRAY_MAP      : Z3_decl_kind
  val Z3_OP_ARRAY_DEFAULT  : Z3_decl_kind
  val Z3_OP_SET_UNION      : Z3_decl_kind
  val Z3_OP_SET_INTERSECT  : Z3_decl_kind
  val Z3_OP_SET_DIFFERENCE : Z3_decl_kind
  val Z3_OP_SET_COMPLEMENT : Z3_decl_kind
  val Z3_OP_SET_SUBSET     : Z3_decl_kind
  val Z3_OP_AS_ARRAY       : Z3_decl_kind
  (* Bit-vectors *)
  val Z3_OP_BNUM           : Z3_decl_kind
  val Z3_OP_BIT1           : Z3_decl_kind
  val Z3_OP_BIT0           : Z3_decl_kind
  val Z3_OP_BNEG           : Z3_decl_kind
  val Z3_OP_BADD           : Z3_decl_kind
  val Z3_OP_BSUB           : Z3_decl_kind
  val Z3_OP_BMUL           : Z3_decl_kind
  val Z3_OP_BSDIV          : Z3_decl_kind
  val Z3_OP_BUDIV          : Z3_decl_kind
  val Z3_OP_BSREM          : Z3_decl_kind
  val Z3_OP_BUREM          : Z3_decl_kind
  val Z3_OP_BSMOD          : Z3_decl_kind
  (*
   * special functions to record the division by 0 cases
   * these are internal functions
   *)
  val Z3_OP_BSDIV0           : Z3_decl_kind
  val Z3_OP_BUDIV0           : Z3_decl_kind
  val Z3_OP_BSREM0           : Z3_decl_kind
  val Z3_OP_BUREM0           : Z3_decl_kind
  val Z3_OP_BSMOD0           : Z3_decl_kind
  val Z3_OP_ULEQ             : Z3_decl_kind
  val Z3_OP_SLEQ             : Z3_decl_kind
  val Z3_OP_UGEQ             : Z3_decl_kind
  val Z3_OP_SGEQ             : Z3_decl_kind
  val Z3_OP_ULT              : Z3_decl_kind
  val Z3_OP_SLT              : Z3_decl_kind
  val Z3_OP_UGT              : Z3_decl_kind
  val Z3_OP_SGT              : Z3_decl_kind
  val Z3_OP_BAND             : Z3_decl_kind
  val Z3_OP_BOR              : Z3_decl_kind
  val Z3_OP_BNOT             : Z3_decl_kind
  val Z3_OP_BXOR             : Z3_decl_kind
  val Z3_OP_BNAND            : Z3_decl_kind
  val Z3_OP_BNOR             : Z3_decl_kind
  val Z3_OP_BXNOR            : Z3_decl_kind
  val Z3_OP_CONCAT           : Z3_decl_kind
  val Z3_OP_SIGN_EXT         : Z3_decl_kind
  val Z3_OP_ZERO_EXT         : Z3_decl_kind
  val Z3_OP_EXTRACT          : Z3_decl_kind
  val Z3_OP_REPEAT           : Z3_decl_kind
  val Z3_OP_BREDOR           : Z3_decl_kind
  val Z3_OP_BREDAND          : Z3_decl_kind
  val Z3_OP_BCOMP            : Z3_decl_kind
  val Z3_OP_BSHL             : Z3_decl_kind
  val Z3_OP_BLSHR            : Z3_decl_kind
  val Z3_OP_BASHR            : Z3_decl_kind
  val Z3_OP_ROTATE_LEFT      : Z3_decl_kind
  val Z3_OP_ROTATE_RIGHT     : Z3_decl_kind
  val Z3_OP_EXT_ROTATE_LEFT  : Z3_decl_kind
  val Z3_OP_EXT_ROTATE_RIGHT : Z3_decl_kind
  val Z3_OP_INT2BV           : Z3_decl_kind
  val Z3_OP_BV2INT           : Z3_decl_kind
  val Z3_OP_CARRY            : Z3_decl_kind
  val Z3_OP_XOR3             : Z3_decl_kind
  (* Proofs *)
  val Z3_OP_PR_UNDEF             : Z3_decl_kind
  val Z3_OP_PR_TRUE              : Z3_decl_kind
  val Z3_OP_PR_ASSERTED          : Z3_decl_kind
  val Z3_OP_PR_GOAL              : Z3_decl_kind
  val Z3_OP_PR_MODUS_PONENS      : Z3_decl_kind
  val Z3_OP_PR_REFLEXIVITY       : Z3_decl_kind
  val Z3_OP_PR_SYMMETRY          : Z3_decl_kind
  val Z3_OP_PR_TRANSITIVITY      : Z3_decl_kind
  val Z3_OP_PR_TRANSITIVITY_STAR : Z3_decl_kind
  val Z3_OP_PR_MONOTONICITY      : Z3_decl_kind
  val Z3_OP_PR_QUANT_INTRO       : Z3_decl_kind
  val Z3_OP_PR_DISTRIBUTIVITY    : Z3_decl_kind
  val Z3_OP_PR_AND_ELIM          : Z3_decl_kind
  val Z3_OP_PR_NOT_OR_ELIM       : Z3_decl_kind
  val Z3_OP_PR_REWRITE           : Z3_decl_kind
  val Z3_OP_PR_REWRITE_STAR      : Z3_decl_kind
  val Z3_OP_PR_PULL_QUANT        : Z3_decl_kind
  val Z3_OP_PR_PULL_QUANT_STAR   : Z3_decl_kind
  val Z3_OP_PR_PUSH_QUANT        : Z3_decl_kind
  val Z3_OP_PR_ELIM_UNUSED_VARS  : Z3_decl_kind
  val Z3_OP_PR_DER               : Z3_decl_kind
  val Z3_OP_PR_QUANT_INST        : Z3_decl_kind
  val Z3_OP_PR_HYPOTHESIS        : Z3_decl_kind
  val Z3_OP_PR_LEMMA             : Z3_decl_kind
  val Z3_OP_PR_UNIT_RESOLUTION   : Z3_decl_kind
  val Z3_OP_PR_IFF_TRUE          : Z3_decl_kind
  val Z3_OP_PR_IFF_FALSE         : Z3_decl_kind
  val Z3_OP_PR_COMMUTATIVITY     : Z3_decl_kind
  val Z3_OP_PR_DEF_AXIOM         : Z3_decl_kind
  val Z3_OP_PR_DEF_INTRO         : Z3_decl_kind
  val Z3_OP_PR_APPLY_DEF         : Z3_decl_kind
  val Z3_OP_PR_IFF_OEQ           : Z3_decl_kind
  val Z3_OP_PR_NNF_POS           : Z3_decl_kind
  val Z3_OP_PR_NNF_NEG           : Z3_decl_kind
  val Z3_OP_PR_NNF_STAR          : Z3_decl_kind
  val Z3_OP_PR_CNF_STAR          : Z3_decl_kind
  val Z3_OP_PR_SKOLEMIZE         : Z3_decl_kind
  val Z3_OP_PR_MODUS_PONENS_OEQ  : Z3_decl_kind
  val Z3_OP_PR_TH_LEMMA          : Z3_decl_kind
  val Z3_OP_PR_HYPER_RESOLVE     : Z3_decl_kind
  (* Sequences *)
  val Z3_OP_RA_STORE           : Z3_decl_kind
  val Z3_OP_RA_EMPTY           : Z3_decl_kind
  val Z3_OP_RA_IS_EMPTY        : Z3_decl_kind
  val Z3_OP_RA_JOIN            : Z3_decl_kind
  val Z3_OP_RA_UNION           : Z3_decl_kind
  val Z3_OP_RA_WIDEN           : Z3_decl_kind
  val Z3_OP_RA_PROJECT         : Z3_decl_kind
  val Z3_OP_RA_FILTER          : Z3_decl_kind
  val Z3_OP_RA_NEGATION_FILTER : Z3_decl_kind
  val Z3_OP_RA_RENAME          : Z3_decl_kind
  val Z3_OP_RA_COMPLEMENT      : Z3_decl_kind
  val Z3_OP_RA_SELECT          : Z3_decl_kind
  val Z3_OP_RA_CLONE           : Z3_decl_kind
  val Z3_OP_FD_LT              : Z3_decl_kind
  (* Auxiliary *)
  val Z3_OP_LABEL     : Z3_decl_kind
  val Z3_OP_LABEL_LIT : Z3_decl_kind
  (* Datatypes *)
  val Z3_OP_DT_CONSTRUCTOR : Z3_decl_kind
  val Z3_OP_DT_RECOGNISER  : Z3_decl_kind
  val Z3_OP_DT_ACCESSOR    : Z3_decl_kind
  val Z3_OP_UNINTERPRETED  : Z3_decl_kind

  eqtype Z3_param_kind
  val Z3_PK_UINT    : Z3_param_kind
  val Z3_PK_BOOL    : Z3_param_kind
  val Z3_PK_DOUBLE  : Z3_param_kind
  val Z3_PK_SYMBOL  : Z3_param_kind
  val Z3_PK_STRING  : Z3_param_kind
  val Z3_PK_OTHER   : Z3_param_kind
  val Z3_PK_INVALID : Z3_param_kind

  eqtype Z3_search_failure
  val Z3_NO_FAILURE       : Z3_search_failure
  val Z3_UNKNOWN          : Z3_search_failure
  val Z3_TIMEOUT          : Z3_search_failure
  val Z3_MEMOUT_WATERMARK : Z3_search_failure
  val Z3_CANCELED         : Z3_search_failure
  val Z3_NUM_CONFLICTS    : Z3_search_failure
  val Z3_THEORY           : Z3_search_failure
  val Z3_QUANTIFIERS      : Z3_search_failure

  eqtype Z3_ast_print_mode
  val Z3_PRINT_SMTLIB_FULL       : Z3_ast_print_mode
  val Z3_PRINT_LOW_LEVEL         : Z3_ast_print_mode
  val Z3_PRINT_SMTLIB_COMPLIANT  : Z3_ast_print_mode
  val Z3_PRINT_SMTLIB2_COMPLIANT : Z3_ast_print_mode

  eqtype Z3_error_code
  val Z3_OK                : Z3_error_code
  val Z3_SORT_ERROR        : Z3_error_code
  val Z3_IOB               : Z3_error_code
  val Z3_INVALID_ARG       : Z3_error_code
  val Z3_PARSER_ERROR      : Z3_error_code
  val Z3_NO_PARSER         : Z3_error_code
  val Z3_INVALID_PATTERN   : Z3_error_code
  val Z3_MEMOUT_FAIL       : Z3_error_code
  val Z3_FILE_ACCESS_ERROR : Z3_error_code
  val Z3_INTERNAL_FATAL    : Z3_error_code
  val Z3_INVALID_USAGE     : Z3_error_code
  val Z3_DEC_REF_ERROR     : Z3_error_code
  val Z3_EXCEPTION         : Z3_error_code

  eqtype Z3_goal_prec
  val Z3_GOAL_PRECISE    : Z3_goal_prec
  val Z3_GOAL_UNDER      : Z3_goal_prec
  val Z3_GOAL_OVER       : Z3_goal_prec
  val Z3_GOAL_UNDER_OVER : Z3_goal_prec
end


