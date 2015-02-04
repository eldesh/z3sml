
structure Z3_enum :> Z3_ENUM =
struct
  type Z3_lbool = int
  val Z3_L_FALSE = ~1
  val Z3_L_UNDEF =  0
  val Z3_L_TRUE  =  1

  type Z3_symbol_kind = int
  val Z3_INT_SYMBOL    = 0
  val Z3_STRING_SYMBOL = 1

  type Z3_parameter_kind = int
  val Z3_PARAMETER_INT       = 0
  val Z3_PARAMETER_DOUBLE    = 1
  val Z3_PARAMETER_RATIONAL  = 2
  val Z3_PARAMETER_SYMBOL    = 3
  val Z3_PARAMETER_SORT      = 4
  val Z3_PARAMETER_AST       = 5
  val Z3_PARAMETER_FUNC_DECL = 6

  type Z3_sort_kind = int
  val Z3_UNINTERPRETED_SORT = 0
  val Z3_BOOL_SORT          = 1
  val Z3_INT_SORT           = 2
  val Z3_REAL_SORT          = 3
  val Z3_BV_SORT            = 4
  val Z3_ARRAY_SORT         = 5
  val Z3_DATATYPE_SORT      = 6
  val Z3_RELATION_SORT      = 7
  val Z3_FINITE_DOMAIN_SORT = 8
  val Z3_UNKNOWN_SORT       = 1000

  type Z3_ast_kind = int
  val Z3_NUMERAL_AST    = 0
  val Z3_APP_AST        = 1
  val Z3_VAR_AST        = 2
  val Z3_QUANTIFIER_AST = 3
  val Z3_SORT_AST       = 4
  val Z3_FUNC_DECL_AST  = 5
  val Z3_UNKNOWN_AST    = 1000

  type Z3_decl_kind      = int
  (* Basic *)
  val Z3_OP_TRUE     = 0x100
  val Z3_OP_FALSE    = 0x101
  val Z3_OP_EQ       = 0x102
  val Z3_OP_DISTINCT = 0x103
  val Z3_OP_ITE      = 0x104
  val Z3_OP_AND      = 0x105
  val Z3_OP_OR       = 0x106
  val Z3_OP_IFF      = 0x107
  val Z3_OP_XOR      = 0x108
  val Z3_OP_NOT      = 0x109
  val Z3_OP_IMPLIES  = 0x10A
  val Z3_OP_OEQ      = 0x10B
  (* Arithmetic *)
  val Z3_OP_ANUM    = 0x200
  val Z3_OP_AGNUM   = 0x201
  val Z3_OP_LE      = 0x202
  val Z3_OP_GE      = 0x203
  val Z3_OP_LT      = 0x204
  val Z3_OP_GT      = 0x205
  val Z3_OP_ADD     = 0x206
  val Z3_OP_SUB     = 0x207
  val Z3_OP_UMINUS  = 0x208
  val Z3_OP_MUL     = 0x209
  val Z3_OP_DIV     = 0x20A
  val Z3_OP_IDIV    = 0x20B
  val Z3_OP_REM     = 0x20C
  val Z3_OP_MOD     = 0x20D
  val Z3_OP_TO_REAL = 0x20E
  val Z3_OP_TO_INT  = 0x20F
  val Z3_OP_IS_INT  = 0x210
  val Z3_OP_POWER   = 0x211
  (* Arrays & Sets *)
  val Z3_OP_STORE          = 0x300
  val Z3_OP_SELECT         = 0x301
  val Z3_OP_CONST_ARRAY    = 0x302
  val Z3_OP_ARRAY_MAP      = 0x303
  val Z3_OP_ARRAY_DEFAULT  = 0x304
  val Z3_OP_SET_UNION      = 0x305
  val Z3_OP_SET_INTERSECT  = 0x306
  val Z3_OP_SET_DIFFERENCE = 0x307
  val Z3_OP_SET_COMPLEMENT = 0x308
  val Z3_OP_SET_SUBSET     = 0x309
  val Z3_OP_AS_ARRAY       = 0x30A
  (* Bit-vectors *)
  val Z3_OP_BNUM             = 0x400
  val Z3_OP_BIT1             = 0x401
  val Z3_OP_BIT0             = 0x402
  val Z3_OP_BNEG             = 0x403
  val Z3_OP_BADD             = 0x404
  val Z3_OP_BSUB             = 0x405
  val Z3_OP_BMUL             = 0x406
  val Z3_OP_BSDIV            = 0x407
  val Z3_OP_BUDIV            = 0x408
  val Z3_OP_BSREM            = 0x409
  val Z3_OP_BUREM            = 0x40A
  val Z3_OP_BSMOD            = 0x40B
  (*
   * special functions to record the division by 0 cases
   * these are internal functions
   *)
  val Z3_OP_BSDIV0           = 0x40C
  val Z3_OP_BUDIV0           = 0x40D
  val Z3_OP_BSREM0           = 0x40E
  val Z3_OP_BUREM0           = 0x40F
  val Z3_OP_BSMOD0           = 0x410
  val Z3_OP_ULEQ             = 0x411
  val Z3_OP_SLEQ             = 0x412
  val Z3_OP_UGEQ             = 0x413
  val Z3_OP_SGEQ             = 0x414
  val Z3_OP_ULT              = 0x415
  val Z3_OP_SLT              = 0x416
  val Z3_OP_UGT              = 0x417
  val Z3_OP_SGT              = 0x418
  val Z3_OP_BAND             = 0x419
  val Z3_OP_BOR              = 0x41A
  val Z3_OP_BNOT             = 0x41B
  val Z3_OP_BXOR             = 0x41C
  val Z3_OP_BNAND            = 0x41D
  val Z3_OP_BNOR             = 0x41E
  val Z3_OP_BXNOR            = 0x41F
  val Z3_OP_CONCAT           = 0x420
  val Z3_OP_SIGN_EXT         = 0x421
  val Z3_OP_ZERO_EXT         = 0x422
  val Z3_OP_EXTRACT          = 0x423
  val Z3_OP_REPEAT           = 0x424
  val Z3_OP_BREDOR           = 0x425
  val Z3_OP_BREDAND          = 0x426
  val Z3_OP_BCOMP            = 0x427
  val Z3_OP_BSHL             = 0x428
  val Z3_OP_BLSHR            = 0x429
  val Z3_OP_BASHR            = 0x42A
  val Z3_OP_ROTATE_LEFT      = 0x42B
  val Z3_OP_ROTATE_RIGHT     = 0x42C
  val Z3_OP_EXT_ROTATE_LEFT  = 0x42D
  val Z3_OP_EXT_ROTATE_RIGHT = 0x42E
  val Z3_OP_INT2BV           = 0x42F
  val Z3_OP_BV2INT           = 0x430
  val Z3_OP_CARRY            = 0x431
  val Z3_OP_XOR3             = 0x432
  (* Proofs *)
  val Z3_OP_PR_UNDEF             = 0x500
  val Z3_OP_PR_TRUE              = 0x501
  val Z3_OP_PR_ASSERTED          = 0x502
  val Z3_OP_PR_GOAL              = 0x503
  val Z3_OP_PR_MODUS_PONENS      = 0x504
  val Z3_OP_PR_REFLEXIVITY       = 0x505
  val Z3_OP_PR_SYMMETRY          = 0x506
  val Z3_OP_PR_TRANSITIVITY      = 0x507
  val Z3_OP_PR_TRANSITIVITY_STAR = 0x508
  val Z3_OP_PR_MONOTONICITY      = 0x509
  val Z3_OP_PR_QUANT_INTRO       = 0x50A
  val Z3_OP_PR_DISTRIBUTIVITY    = 0x50B
  val Z3_OP_PR_AND_ELIM          = 0x50C
  val Z3_OP_PR_NOT_OR_ELIM       = 0x50D
  val Z3_OP_PR_REWRITE           = 0x50E
  val Z3_OP_PR_REWRITE_STAR      = 0x50F
  val Z3_OP_PR_PULL_QUANT        = 0x510
  val Z3_OP_PR_PULL_QUANT_STAR   = 0x511
  val Z3_OP_PR_PUSH_QUANT        = 0x512
  val Z3_OP_PR_ELIM_UNUSED_VARS  = 0x513
  val Z3_OP_PR_DER               = 0x514
  val Z3_OP_PR_QUANT_INST        = 0x515
  val Z3_OP_PR_HYPOTHESIS        = 0x516
  val Z3_OP_PR_LEMMA             = 0x517
  val Z3_OP_PR_UNIT_RESOLUTION   = 0x518
  val Z3_OP_PR_IFF_TRUE          = 0x519
  val Z3_OP_PR_IFF_FALSE         = 0x51A
  val Z3_OP_PR_COMMUTATIVITY     = 0x51B
  val Z3_OP_PR_DEF_AXIOM         = 0x51C
  val Z3_OP_PR_DEF_INTRO         = 0x51D
  val Z3_OP_PR_APPLY_DEF         = 0x51E
  val Z3_OP_PR_IFF_OEQ           = 0x51F
  val Z3_OP_PR_NNF_POS           = 0x520
  val Z3_OP_PR_NNF_NEG           = 0x521
  val Z3_OP_PR_NNF_STAR          = 0x522
  val Z3_OP_PR_CNF_STAR          = 0x523
  val Z3_OP_PR_SKOLEMIZE         = 0x524
  val Z3_OP_PR_MODUS_PONENS_OEQ  = 0x525
  val Z3_OP_PR_TH_LEMMA          = 0x526
  val Z3_OP_PR_HYPER_RESOLVE     = 0x527
  (* Sequences *)
  val Z3_OP_RA_STORE           = 0x600
  val Z3_OP_RA_EMPTY           = 0x601
  val Z3_OP_RA_IS_EMPTY        = 0x602
  val Z3_OP_RA_JOIN            = 0x603
  val Z3_OP_RA_UNION           = 0x604
  val Z3_OP_RA_WIDEN           = 0x605
  val Z3_OP_RA_PROJECT         = 0x606
  val Z3_OP_RA_FILTER          = 0x607
  val Z3_OP_RA_NEGATION_FILTER = 0x608
  val Z3_OP_RA_RENAME          = 0x609
  val Z3_OP_RA_COMPLEMENT      = 0x60A
  val Z3_OP_RA_SELECT          = 0x60B
  val Z3_OP_RA_CLONE           = 0x60C
  val Z3_OP_FD_LT              = 0x60D
  (* Auxiliary *)
  val Z3_OP_LABEL     = 0x700
  val Z3_OP_LABEL_LIT = 0x701
  (* Datatypes *)
  val Z3_OP_DT_CONSTRUCTOR = 0x800
  val Z3_OP_DT_RECOGNISER  = 0x801
  val Z3_OP_DT_ACCESSOR    = 0x802
  val Z3_OP_UNINTERPRETED  = 0x803

  type Z3_param_kind = int
  val Z3_PK_UINT    = 0
  val Z3_PK_BOOL    = 1
  val Z3_PK_DOUBLE  = 2
  val Z3_PK_SYMBOL  = 3
  val Z3_PK_STRING  = 4
  val Z3_PK_OTHER   = 5
  val Z3_PK_INVALID = 6

  type Z3_search_failure = int
  val Z3_NO_FAILURE       = 0
  val Z3_UNKNOWN          = 1
  val Z3_TIMEOUT          = 2
  val Z3_MEMOUT_WATERMARK = 3
  val Z3_CANCELED         = 4
  val Z3_NUM_CONFLICTS    = 5
  val Z3_THEORY           = 6
  val Z3_QUANTIFIERS      = 7

  type Z3_ast_print_mode = int
  val Z3_PRINT_SMTLIB_FULL       = 0
  val Z3_PRINT_LOW_LEVEL         = 1
  val Z3_PRINT_SMTLIB_COMPLIANT  = 2
  val Z3_PRINT_SMTLIB2_COMPLIANT = 3

  type Z3_error_code = int
  val Z3_OK                = 0
  val Z3_SORT_ERROR        = 1
  val Z3_IOB               = 2
  val Z3_INVALID_ARG       = 3
  val Z3_PARSER_ERROR      = 4
  val Z3_NO_PARSER         = 5
  val Z3_INVALID_PATTERN   = 6
  val Z3_MEMOUT_FAIL       = 7
  val Z3_FILE_ACCESS_ERROR = 8
  val Z3_INTERNAL_FATAL    = 9
  val Z3_INVALID_USAGE     = 10
  val Z3_DEC_REF_ERROR     = 11
  val Z3_EXCEPTION         = 12

  type Z3_goal_prec      = int
  val Z3_GOAL_PRECISE    = 0
  val Z3_GOAL_UNDER      = 1
  val Z3_GOAL_OVER       = 2
  val Z3_GOAL_UNDER_OVER = 3
end


