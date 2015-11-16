
structure Z3_DomainError = struct
  exception EnumDomain of int
end

structure Z3_lbool = struct
  datatype t = Z3_L_FALSE
             | Z3_L_UNDEF
             | Z3_L_TRUE

  fun fromInt n =
    case n
      of ~1 => Z3_L_FALSE
       |  0 => Z3_L_UNDEF
       |  1 => Z3_L_TRUE
       |  n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_L_FALSE => ~1
       | Z3_L_UNDEF =>  0
       | Z3_L_TRUE  =>  1
end

structure Z3_symbol_kind = struct
  datatype t = Z3_INT_SYMBOL
             | Z3_STRING_SYMBOL

  fun fromInt n =
    case n
      of 0 => Z3_INT_SYMBOL
       | 1 => Z3_STRING_SYMBOL
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_INT_SYMBOL    => 0
       | Z3_STRING_SYMBOL => 1
end

structure Z3_parameter_kind = struct
  datatype t = Z3_PARAMETER_INT
             | Z3_PARAMETER_DOUBLE
             | Z3_PARAMETER_RATIONAL
             | Z3_PARAMETER_SYMBOL
             | Z3_PARAMETER_SORT
             | Z3_PARAMETER_AST
             | Z3_PARAMETER_FUNC_DECL

  fun fromInt n =
    case n
      of 0 => Z3_PARAMETER_INT
       | 1 => Z3_PARAMETER_DOUBLE
       | 2 => Z3_PARAMETER_RATIONAL
       | 3 => Z3_PARAMETER_SYMBOL
       | 4 => Z3_PARAMETER_SORT
       | 5 => Z3_PARAMETER_AST
       | 6 => Z3_PARAMETER_FUNC_DECL
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_PARAMETER_INT       => 0
       | Z3_PARAMETER_DOUBLE    => 1
       | Z3_PARAMETER_RATIONAL  => 2
       | Z3_PARAMETER_SYMBOL    => 3
       | Z3_PARAMETER_SORT      => 4
       | Z3_PARAMETER_AST       => 5
       | Z3_PARAMETER_FUNC_DECL => 6
end

structure Z3_sort_kind = struct
  datatype t = Z3_UNINTERPRETED_SORT
             | Z3_BOOL_SORT
             | Z3_INT_SORT
             | Z3_REAL_SORT
             | Z3_BV_SORT
             | Z3_ARRAY_SORT
             | Z3_DATATYPE_SORT
             | Z3_RELATION_SORT
             | Z3_FINITE_DOMAIN_SORT
             | Z3_UNKNOWN_SORT

  fun fromInt n =
    case n
      of 0 => Z3_UNINTERPRETED_SORT
       | 1 => Z3_BOOL_SORT
       | 2 => Z3_INT_SORT
       | 3 => Z3_REAL_SORT
       | 4 => Z3_BV_SORT
       | 5 => Z3_ARRAY_SORT
       | 6 => Z3_DATATYPE_SORT
       | 7 => Z3_RELATION_SORT
       | 8 => Z3_FINITE_DOMAIN_SORT
       | 1000 => Z3_UNKNOWN_SORT
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_UNINTERPRETED_SORT => 0
       | Z3_BOOL_SORT          => 1
       | Z3_INT_SORT           => 2
       | Z3_REAL_SORT          => 3
       | Z3_BV_SORT            => 4
       | Z3_ARRAY_SORT         => 5
       | Z3_DATATYPE_SORT      => 6
       | Z3_RELATION_SORT      => 7
       | Z3_FINITE_DOMAIN_SORT => 8
       | Z3_UNKNOWN_SORT       => 1000
end

structure Z3_ast_kind = struct
  datatype t = Z3_NUMERAL_AST
             | Z3_APP_AST
             | Z3_VAR_AST
             | Z3_QUANTIFIER_AST
             | Z3_SORT_AST
             | Z3_FUNC_DECL_AST
             | Z3_UNKNOWN_AST

  fun fromInt n =
    case n
      of 0 => Z3_NUMERAL_AST
       | 1 => Z3_APP_AST
       | 2 => Z3_VAR_AST
       | 3 => Z3_QUANTIFIER_AST
       | 4 => Z3_SORT_AST
       | 5 => Z3_FUNC_DECL_AST
       | 1000 => Z3_UNKNOWN_AST
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_NUMERAL_AST    => 0
       | Z3_APP_AST        => 1
       | Z3_VAR_AST        => 2
       | Z3_QUANTIFIER_AST => 3
       | Z3_SORT_AST       => 4
       | Z3_FUNC_DECL_AST  => 5
       | Z3_UNKNOWN_AST    => 1000
end

structure Z3_decl_kind = struct
  datatype t = (* Basic *)
               Z3_OP_TRUE
             | Z3_OP_FALSE
             | Z3_OP_EQ
             | Z3_OP_DISTINCT
             | Z3_OP_ITE
             | Z3_OP_AND
             | Z3_OP_OR
             | Z3_OP_IFF
             | Z3_OP_XOR
             | Z3_OP_NOT
             | Z3_OP_IMPLIES
             | Z3_OP_OEQ
             (* Arithmetic *)
             | Z3_OP_ANUM
             | Z3_OP_AGNUM
             | Z3_OP_LE
             | Z3_OP_GE
             | Z3_OP_LT
             | Z3_OP_GT
             | Z3_OP_ADD
             | Z3_OP_SUB
             | Z3_OP_UMINUS
             | Z3_OP_MUL
             | Z3_OP_DIV
             | Z3_OP_IDIV
             | Z3_OP_REM
             | Z3_OP_MOD
             | Z3_OP_TO_REAL
             | Z3_OP_TO_INT
             | Z3_OP_IS_INT
             | Z3_OP_POWER
             (* Arrays & Sets *)
             | Z3_OP_STORE
             | Z3_OP_SELECT
             | Z3_OP_CONST_ARRAY
             | Z3_OP_ARRAY_MAP
             | Z3_OP_ARRAY_DEFAULT
             | Z3_OP_SET_UNION
             | Z3_OP_SET_INTERSECT
             | Z3_OP_SET_DIFFERENCE
             | Z3_OP_SET_COMPLEMENT
             | Z3_OP_SET_SUBSET
             | Z3_OP_AS_ARRAY
             (* Bit-vectors *)
             | Z3_OP_BNUM
             | Z3_OP_BIT1
             | Z3_OP_BIT0
             | Z3_OP_BNEG
             | Z3_OP_BADD
             | Z3_OP_BSUB
             | Z3_OP_BMUL
             | Z3_OP_BSDIV
             | Z3_OP_BUDIV
             | Z3_OP_BSREM
             | Z3_OP_BUREM
             | Z3_OP_BSMOD
             (*
             * special functions to record the division by 0 cases
             * these are internal functions
             *)
             | Z3_OP_BSDIV0
             | Z3_OP_BUDIV0
             | Z3_OP_BSREM0
             | Z3_OP_BUREM0
             | Z3_OP_BSMOD0
             | Z3_OP_ULEQ
             | Z3_OP_SLEQ
             | Z3_OP_UGEQ
             | Z3_OP_SGEQ
             | Z3_OP_ULT
             | Z3_OP_SLT
             | Z3_OP_UGT
             | Z3_OP_SGT
             | Z3_OP_BAND
             | Z3_OP_BOR
             | Z3_OP_BNOT
             | Z3_OP_BXOR
             | Z3_OP_BNAND
             | Z3_OP_BNOR
             | Z3_OP_BXNOR
             | Z3_OP_CONCAT
             | Z3_OP_SIGN_EXT
             | Z3_OP_ZERO_EXT
             | Z3_OP_EXTRACT
             | Z3_OP_REPEAT
             | Z3_OP_BREDOR
             | Z3_OP_BREDAND
             | Z3_OP_BCOMP
             | Z3_OP_BSHL
             | Z3_OP_BLSHR
             | Z3_OP_BASHR
             | Z3_OP_ROTATE_LEFT
             | Z3_OP_ROTATE_RIGHT
             | Z3_OP_EXT_ROTATE_LEFT
             | Z3_OP_EXT_ROTATE_RIGHT
             | Z3_OP_INT2BV
             | Z3_OP_BV2INT
             | Z3_OP_CARRY
             | Z3_OP_XOR3
             (* Proofs *)
             | Z3_OP_PR_UNDEF
             | Z3_OP_PR_TRUE
             | Z3_OP_PR_ASSERTED
             | Z3_OP_PR_GOAL
             | Z3_OP_PR_MODUS_PONENS
             | Z3_OP_PR_REFLEXIVITY
             | Z3_OP_PR_SYMMETRY
             | Z3_OP_PR_TRANSITIVITY
             | Z3_OP_PR_TRANSITIVITY_STAR
             | Z3_OP_PR_MONOTONICITY
             | Z3_OP_PR_QUANT_INTRO
             | Z3_OP_PR_DISTRIBUTIVITY
             | Z3_OP_PR_AND_ELIM
             | Z3_OP_PR_NOT_OR_ELIM
             | Z3_OP_PR_REWRITE
             | Z3_OP_PR_REWRITE_STAR
             | Z3_OP_PR_PULL_QUANT
             | Z3_OP_PR_PULL_QUANT_STAR
             | Z3_OP_PR_PUSH_QUANT
             | Z3_OP_PR_ELIM_UNUSED_VARS
             | Z3_OP_PR_DER
             | Z3_OP_PR_QUANT_INST
             | Z3_OP_PR_HYPOTHESIS
             | Z3_OP_PR_LEMMA
             | Z3_OP_PR_UNIT_RESOLUTION
             | Z3_OP_PR_IFF_TRUE
             | Z3_OP_PR_IFF_FALSE
             | Z3_OP_PR_COMMUTATIVITY
             | Z3_OP_PR_DEF_AXIOM
             | Z3_OP_PR_DEF_INTRO
             | Z3_OP_PR_APPLY_DEF
             | Z3_OP_PR_IFF_OEQ
             | Z3_OP_PR_NNF_POS
             | Z3_OP_PR_NNF_NEG
             | Z3_OP_PR_NNF_STAR
             | Z3_OP_PR_CNF_STAR
             | Z3_OP_PR_SKOLEMIZE
             | Z3_OP_PR_MODUS_PONENS_OEQ
             | Z3_OP_PR_TH_LEMMA
             | Z3_OP_PR_HYPER_RESOLVE
             (* Sequences *)
             | Z3_OP_RA_STORE
             | Z3_OP_RA_EMPTY
             | Z3_OP_RA_IS_EMPTY
             | Z3_OP_RA_JOIN
             | Z3_OP_RA_UNION
             | Z3_OP_RA_WIDEN
             | Z3_OP_RA_PROJECT
             | Z3_OP_RA_FILTER
             | Z3_OP_RA_NEGATION_FILTER
             | Z3_OP_RA_RENAME
             | Z3_OP_RA_COMPLEMENT
             | Z3_OP_RA_SELECT
             | Z3_OP_RA_CLONE
             | Z3_OP_FD_LT
             (* Auxiliary *)
             | Z3_OP_LABEL
             | Z3_OP_LABEL_LIT
             (* Datatypes *)
             | Z3_OP_DT_CONSTRUCTOR
             | Z3_OP_DT_RECOGNISER
             | Z3_OP_DT_ACCESSOR
             | Z3_OP_UNINTERPRETED

  fun fromInt n =
    case n
      of 0x100 => Z3_OP_TRUE (* Basic *)
       | 0x101 => Z3_OP_FALSE
       | 0x102 => Z3_OP_EQ
       | 0x103 => Z3_OP_DISTINCT
       | 0x104 => Z3_OP_ITE
       | 0x105 => Z3_OP_AND
       | 0x106 => Z3_OP_OR
       | 0x107 => Z3_OP_IFF
       | 0x108 => Z3_OP_XOR
       | 0x109 => Z3_OP_NOT
       | 0x10A => Z3_OP_IMPLIES
       | 0x10B => Z3_OP_OEQ
       (* Arithmetic *)
       | 0x200 => Z3_OP_ANUM
       | 0x201 => Z3_OP_AGNUM
       | 0x202 => Z3_OP_LE
       | 0x203 => Z3_OP_GE
       | 0x204 => Z3_OP_LT
       | 0x205 => Z3_OP_GT
       | 0x206 => Z3_OP_ADD
       | 0x207 => Z3_OP_SUB
       | 0x208 => Z3_OP_UMINUS
       | 0x209 => Z3_OP_MUL
       | 0x20A => Z3_OP_DIV
       | 0x20B => Z3_OP_IDIV
       | 0x20C => Z3_OP_REM
       | 0x20D => Z3_OP_MOD
       | 0x20E => Z3_OP_TO_REAL
       | 0x20F => Z3_OP_TO_INT
       | 0x210 => Z3_OP_IS_INT
       | 0x211 => Z3_OP_POWER
       (* Arrays & Sets *)
       | 0x300 => Z3_OP_STORE
       | 0x301 => Z3_OP_SELECT
       | 0x302 => Z3_OP_CONST_ARRAY
       | 0x303 => Z3_OP_ARRAY_MAP
       | 0x304 => Z3_OP_ARRAY_DEFAULT
       | 0x305 => Z3_OP_SET_UNION
       | 0x306 => Z3_OP_SET_INTERSECT
       | 0x307 => Z3_OP_SET_DIFFERENCE
       | 0x308 => Z3_OP_SET_COMPLEMENT
       | 0x309 => Z3_OP_SET_SUBSET
       | 0x30A => Z3_OP_AS_ARRAY
       (* Bit-vectors *)
       | 0x400 => Z3_OP_BNUM
       | 0x401 => Z3_OP_BIT1
       | 0x402 => Z3_OP_BIT0
       | 0x403 => Z3_OP_BNEG
       | 0x404 => Z3_OP_BADD
       | 0x405 => Z3_OP_BSUB
       | 0x406 => Z3_OP_BMUL
       | 0x407 => Z3_OP_BSDIV
       | 0x408 => Z3_OP_BUDIV
       | 0x409 => Z3_OP_BSREM
       | 0x40A => Z3_OP_BUREM
       | 0x40B => Z3_OP_BSMOD
       (*
       * special functions to record the division by 0 cases
       * these are internal functions
       *)
       | 0x40C => Z3_OP_BSDIV0
       | 0x40D => Z3_OP_BUDIV0
       | 0x40E => Z3_OP_BSREM0
       | 0x40F => Z3_OP_BUREM0
       | 0x410 => Z3_OP_BSMOD0
       | 0x411 => Z3_OP_ULEQ
       | 0x412 => Z3_OP_SLEQ
       | 0x413 => Z3_OP_UGEQ
       | 0x414 => Z3_OP_SGEQ
       | 0x415 => Z3_OP_ULT
       | 0x416 => Z3_OP_SLT
       | 0x417 => Z3_OP_UGT
       | 0x418 => Z3_OP_SGT
       | 0x419 => Z3_OP_BAND
       | 0x41A => Z3_OP_BOR
       | 0x41B => Z3_OP_BNOT
       | 0x41C => Z3_OP_BXOR
       | 0x41D => Z3_OP_BNAND
       | 0x41E => Z3_OP_BNOR
       | 0x41F => Z3_OP_BXNOR
       | 0x420 => Z3_OP_CONCAT
       | 0x421 => Z3_OP_SIGN_EXT
       | 0x422 => Z3_OP_ZERO_EXT
       | 0x423 => Z3_OP_EXTRACT
       | 0x424 => Z3_OP_REPEAT
       | 0x425 => Z3_OP_BREDOR
       | 0x426 => Z3_OP_BREDAND
       | 0x427 => Z3_OP_BCOMP
       | 0x428 => Z3_OP_BSHL
       | 0x429 => Z3_OP_BLSHR
       | 0x42A => Z3_OP_BASHR
       | 0x42B => Z3_OP_ROTATE_LEFT
       | 0x42C => Z3_OP_ROTATE_RIGHT
       | 0x42D => Z3_OP_EXT_ROTATE_LEFT
       | 0x42E => Z3_OP_EXT_ROTATE_RIGHT
       | 0x42F => Z3_OP_INT2BV
       | 0x430 => Z3_OP_BV2INT
       | 0x431 => Z3_OP_CARRY
       | 0x432 => Z3_OP_XOR3
       (* Proofs *)
       | 0x500 => Z3_OP_PR_UNDEF
       | 0x501 => Z3_OP_PR_TRUE
       | 0x502 => Z3_OP_PR_ASSERTED
       | 0x503 => Z3_OP_PR_GOAL
       | 0x504 => Z3_OP_PR_MODUS_PONENS
       | 0x505 => Z3_OP_PR_REFLEXIVITY
       | 0x506 => Z3_OP_PR_SYMMETRY
       | 0x507 => Z3_OP_PR_TRANSITIVITY
       | 0x508 => Z3_OP_PR_TRANSITIVITY_STAR
       | 0x509 => Z3_OP_PR_MONOTONICITY
       | 0x50A => Z3_OP_PR_QUANT_INTRO
       | 0x50B => Z3_OP_PR_DISTRIBUTIVITY
       | 0x50C => Z3_OP_PR_AND_ELIM
       | 0x50D => Z3_OP_PR_NOT_OR_ELIM
       | 0x50E => Z3_OP_PR_REWRITE
       | 0x50F => Z3_OP_PR_REWRITE_STAR
       | 0x510 => Z3_OP_PR_PULL_QUANT
       | 0x511 => Z3_OP_PR_PULL_QUANT_STAR
       | 0x512 => Z3_OP_PR_PUSH_QUANT
       | 0x513 => Z3_OP_PR_ELIM_UNUSED_VARS
       | 0x514 => Z3_OP_PR_DER
       | 0x515 => Z3_OP_PR_QUANT_INST
       | 0x516 => Z3_OP_PR_HYPOTHESIS
       | 0x517 => Z3_OP_PR_LEMMA
       | 0x518 => Z3_OP_PR_UNIT_RESOLUTION
       | 0x519 => Z3_OP_PR_IFF_TRUE
       | 0x51A => Z3_OP_PR_IFF_FALSE
       | 0x51B => Z3_OP_PR_COMMUTATIVITY
       | 0x51C => Z3_OP_PR_DEF_AXIOM
       | 0x51D => Z3_OP_PR_DEF_INTRO
       | 0x51E => Z3_OP_PR_APPLY_DEF
       | 0x51F => Z3_OP_PR_IFF_OEQ
       | 0x520 => Z3_OP_PR_NNF_POS
       | 0x521 => Z3_OP_PR_NNF_NEG
       | 0x522 => Z3_OP_PR_NNF_STAR
       | 0x523 => Z3_OP_PR_CNF_STAR
       | 0x524 => Z3_OP_PR_SKOLEMIZE
       | 0x525 => Z3_OP_PR_MODUS_PONENS_OEQ
       | 0x526 => Z3_OP_PR_TH_LEMMA
       | 0x527 => Z3_OP_PR_HYPER_RESOLVE
       (* Sequences *)
       | 0x600 => Z3_OP_RA_STORE
       | 0x601 => Z3_OP_RA_EMPTY
       | 0x602 => Z3_OP_RA_IS_EMPTY
       | 0x603 => Z3_OP_RA_JOIN
       | 0x604 => Z3_OP_RA_UNION
       | 0x605 => Z3_OP_RA_WIDEN
       | 0x606 => Z3_OP_RA_PROJECT
       | 0x607 => Z3_OP_RA_FILTER
       | 0x608 => Z3_OP_RA_NEGATION_FILTER
       | 0x609 => Z3_OP_RA_RENAME
       | 0x60A => Z3_OP_RA_COMPLEMENT
       | 0x60B => Z3_OP_RA_SELECT
       | 0x60C => Z3_OP_RA_CLONE
       | 0x60D => Z3_OP_FD_LT
       (* Auxiliary *)
       | 0x700 => Z3_OP_LABEL
       | 0x701 => Z3_OP_LABEL_LIT
       (* Datatypes *)
       | 0x800 => Z3_OP_DT_CONSTRUCTOR
       | 0x801 => Z3_OP_DT_RECOGNISER
       | 0x802 => Z3_OP_DT_ACCESSOR
       | 0x803 => Z3_OP_UNINTERPRETED
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_OP_TRUE      => 0x100(* Basic *)
       | Z3_OP_FALSE     => 0x101
       | Z3_OP_EQ        => 0x102
       | Z3_OP_DISTINCT  => 0x103
       | Z3_OP_ITE       => 0x104
       | Z3_OP_AND       => 0x105
       | Z3_OP_OR        => 0x106
       | Z3_OP_IFF       => 0x107
       | Z3_OP_XOR       => 0x108
       | Z3_OP_NOT       => 0x109
       | Z3_OP_IMPLIES   => 0x10A
       | Z3_OP_OEQ       => 0x10B
       (* Arithmetic *)
       | Z3_OP_ANUM     => 0x200
       | Z3_OP_AGNUM    => 0x201
       | Z3_OP_LE       => 0x202
       | Z3_OP_GE       => 0x203
       | Z3_OP_LT       => 0x204
       | Z3_OP_GT       => 0x205
       | Z3_OP_ADD      => 0x206
       | Z3_OP_SUB      => 0x207
       | Z3_OP_UMINUS   => 0x208
       | Z3_OP_MUL      => 0x209
       | Z3_OP_DIV      => 0x20A
       | Z3_OP_IDIV     => 0x20B
       | Z3_OP_REM      => 0x20C
       | Z3_OP_MOD      => 0x20D
       | Z3_OP_TO_REAL  => 0x20E
       | Z3_OP_TO_INT   => 0x20F
       | Z3_OP_IS_INT   => 0x210
       | Z3_OP_POWER    => 0x211
       (* Arrays & Sets *)
       | Z3_OP_STORE           => 0x300
       | Z3_OP_SELECT          => 0x301
       | Z3_OP_CONST_ARRAY     => 0x302
       | Z3_OP_ARRAY_MAP       => 0x303
       | Z3_OP_ARRAY_DEFAULT   => 0x304
       | Z3_OP_SET_UNION       => 0x305
       | Z3_OP_SET_INTERSECT   => 0x306
       | Z3_OP_SET_DIFFERENCE  => 0x307
       | Z3_OP_SET_COMPLEMENT  => 0x308
       | Z3_OP_SET_SUBSET      => 0x309
       | Z3_OP_AS_ARRAY        => 0x30A
       (* Bit-vectors *)
       | Z3_OP_BNUM            => 0x400
       | Z3_OP_BIT1            => 0x401
       | Z3_OP_BIT0            => 0x402
       | Z3_OP_BNEG            => 0x403
       | Z3_OP_BADD            => 0x404
       | Z3_OP_BSUB            => 0x405
       | Z3_OP_BMUL            => 0x406
       | Z3_OP_BSDIV           => 0x407
       | Z3_OP_BUDIV           => 0x408
       | Z3_OP_BSREM           => 0x409
       | Z3_OP_BUREM           => 0x40A
       | Z3_OP_BSMOD           => 0x40B
       (*
       * special functions to record the division by 0 cases
       * these are internal functions
       *)
       | Z3_OP_BSDIV0           => 0x40C
       | Z3_OP_BUDIV0           => 0x40D
       | Z3_OP_BSREM0           => 0x40E
       | Z3_OP_BUREM0           => 0x40F
       | Z3_OP_BSMOD0           => 0x410
       | Z3_OP_ULEQ             => 0x411
       | Z3_OP_SLEQ             => 0x412
       | Z3_OP_UGEQ             => 0x413
       | Z3_OP_SGEQ             => 0x414
       | Z3_OP_ULT              => 0x415
       | Z3_OP_SLT              => 0x416
       | Z3_OP_UGT              => 0x417
       | Z3_OP_SGT              => 0x418
       | Z3_OP_BAND             => 0x419
       | Z3_OP_BOR              => 0x41A
       | Z3_OP_BNOT             => 0x41B
       | Z3_OP_BXOR             => 0x41C
       | Z3_OP_BNAND            => 0x41D
       | Z3_OP_BNOR             => 0x41E
       | Z3_OP_BXNOR            => 0x41F
       | Z3_OP_CONCAT           => 0x420
       | Z3_OP_SIGN_EXT         => 0x421
       | Z3_OP_ZERO_EXT         => 0x422
       | Z3_OP_EXTRACT          => 0x423
       | Z3_OP_REPEAT           => 0x424
       | Z3_OP_BREDOR           => 0x425
       | Z3_OP_BREDAND          => 0x426
       | Z3_OP_BCOMP            => 0x427
       | Z3_OP_BSHL             => 0x428
       | Z3_OP_BLSHR            => 0x429
       | Z3_OP_BASHR            => 0x42A
       | Z3_OP_ROTATE_LEFT      => 0x42B
       | Z3_OP_ROTATE_RIGHT     => 0x42C
       | Z3_OP_EXT_ROTATE_LEFT  => 0x42D
       | Z3_OP_EXT_ROTATE_RIGHT => 0x42E
       | Z3_OP_INT2BV           => 0x42F
       | Z3_OP_BV2INT           => 0x430
       | Z3_OP_CARRY            => 0x431
       | Z3_OP_XOR3             => 0x432
       (* Proofs *)
       | Z3_OP_PR_UNDEF             => 0x500
       | Z3_OP_PR_TRUE              => 0x501
       | Z3_OP_PR_ASSERTED          => 0x502
       | Z3_OP_PR_GOAL              => 0x503
       | Z3_OP_PR_MODUS_PONENS      => 0x504
       | Z3_OP_PR_REFLEXIVITY       => 0x505
       | Z3_OP_PR_SYMMETRY          => 0x506
       | Z3_OP_PR_TRANSITIVITY      => 0x507
       | Z3_OP_PR_TRANSITIVITY_STAR => 0x508
       | Z3_OP_PR_MONOTONICITY      => 0x509
       | Z3_OP_PR_QUANT_INTRO       => 0x50A
       | Z3_OP_PR_DISTRIBUTIVITY    => 0x50B
       | Z3_OP_PR_AND_ELIM          => 0x50C
       | Z3_OP_PR_NOT_OR_ELIM       => 0x50D
       | Z3_OP_PR_REWRITE           => 0x50E
       | Z3_OP_PR_REWRITE_STAR      => 0x50F
       | Z3_OP_PR_PULL_QUANT        => 0x510
       | Z3_OP_PR_PULL_QUANT_STAR   => 0x511
       | Z3_OP_PR_PUSH_QUANT        => 0x512
       | Z3_OP_PR_ELIM_UNUSED_VARS  => 0x513
       | Z3_OP_PR_DER               => 0x514
       | Z3_OP_PR_QUANT_INST        => 0x515
       | Z3_OP_PR_HYPOTHESIS        => 0x516
       | Z3_OP_PR_LEMMA             => 0x517
       | Z3_OP_PR_UNIT_RESOLUTION   => 0x518
       | Z3_OP_PR_IFF_TRUE          => 0x519
       | Z3_OP_PR_IFF_FALSE         => 0x51A
       | Z3_OP_PR_COMMUTATIVITY     => 0x51B
       | Z3_OP_PR_DEF_AXIOM         => 0x51C
       | Z3_OP_PR_DEF_INTRO         => 0x51D
       | Z3_OP_PR_APPLY_DEF         => 0x51E
       | Z3_OP_PR_IFF_OEQ           => 0x51F
       | Z3_OP_PR_NNF_POS           => 0x520
       | Z3_OP_PR_NNF_NEG           => 0x521
       | Z3_OP_PR_NNF_STAR          => 0x522
       | Z3_OP_PR_CNF_STAR          => 0x523
       | Z3_OP_PR_SKOLEMIZE         => 0x524
       | Z3_OP_PR_MODUS_PONENS_OEQ  => 0x525
       | Z3_OP_PR_TH_LEMMA          => 0x526
       | Z3_OP_PR_HYPER_RESOLVE     => 0x527
       (* Sequences *)
       | Z3_OP_RA_STORE           => 0x600
       | Z3_OP_RA_EMPTY           => 0x601
       | Z3_OP_RA_IS_EMPTY        => 0x602
       | Z3_OP_RA_JOIN            => 0x603
       | Z3_OP_RA_UNION           => 0x604
       | Z3_OP_RA_WIDEN           => 0x605
       | Z3_OP_RA_PROJECT         => 0x606
       | Z3_OP_RA_FILTER          => 0x607
       | Z3_OP_RA_NEGATION_FILTER => 0x608
       | Z3_OP_RA_RENAME          => 0x609
       | Z3_OP_RA_COMPLEMENT      => 0x60A
       | Z3_OP_RA_SELECT          => 0x60B
       | Z3_OP_RA_CLONE           => 0x60C
       | Z3_OP_FD_LT              => 0x60D
       (* Auxiliary *)
       | Z3_OP_LABEL          => 0x700
       | Z3_OP_LABEL_LIT      => 0x701
       (* Datatypes *)
       | Z3_OP_DT_CONSTRUCTOR => 0x800
       | Z3_OP_DT_RECOGNISER  => 0x801
       | Z3_OP_DT_ACCESSOR    => 0x802
       | Z3_OP_UNINTERPRETED  => 0x803
end

structure Z3_param_kind = struct
  datatype t = Z3_PK_UINT
             | Z3_PK_BOOL
             | Z3_PK_DOUBLE
             | Z3_PK_SYMBOL
             | Z3_PK_STRING
             | Z3_PK_OTHER
             | Z3_PK_INVALID

  fun fromInt n =
    case n
      of 0 => Z3_PK_UINT
       | 1 => Z3_PK_BOOL
       | 2 => Z3_PK_DOUBLE
       | 3 => Z3_PK_SYMBOL
       | 4 => Z3_PK_STRING
       | 5 => Z3_PK_OTHER
       | 6 => Z3_PK_INVALID
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_PK_UINT    => 0
       | Z3_PK_BOOL    => 1
       | Z3_PK_DOUBLE  => 2
       | Z3_PK_SYMBOL  => 3
       | Z3_PK_STRING  => 4
       | Z3_PK_OTHER   => 5
       | Z3_PK_INVALID => 6
end

structure Z3_search_failure = struct
  datatype t = Z3_NO_FAILURE
             | Z3_UNKNOWN
             | Z3_TIMEOUT
             | Z3_MEMOUT_WATERMARK
             | Z3_CANCELED
             | Z3_NUM_CONFLICTS
             | Z3_THEORY
             | Z3_QUANTIFIERS

  fun fromInt n =
    case n
      of 0 => Z3_NO_FAILURE
       | 1 => Z3_UNKNOWN
       | 2 => Z3_TIMEOUT
       | 3 => Z3_MEMOUT_WATERMARK
       | 4 => Z3_CANCELED
       | 5 => Z3_NUM_CONFLICTS
       | 6 => Z3_THEORY
       | 7 => Z3_QUANTIFIERS
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt t =
    case t
      of Z3_NO_FAILURE       => 0
       | Z3_UNKNOWN          => 1
       | Z3_TIMEOUT          => 2
       | Z3_MEMOUT_WATERMARK => 3
       | Z3_CANCELED         => 4
       | Z3_NUM_CONFLICTS    => 5
       | Z3_THEORY           => 6
       | Z3_QUANTIFIERS      => 7
end

structure Z3_ast_print_mode = struct
  datatype t = Z3_PRINT_SMTLIB_FULL
             | Z3_PRINT_LOW_LEVEL
             | Z3_PRINT_SMTLIB_COMPLIANT
             | Z3_PRINT_SMTLIB2_COMPLIANT

  fun fromInt n =
    case n
      of 0 => Z3_PRINT_SMTLIB_FULL
       | 1 => Z3_PRINT_LOW_LEVEL
       | 2 => Z3_PRINT_SMTLIB_COMPLIANT
       | 3 => Z3_PRINT_SMTLIB2_COMPLIANT
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt e =
    case e
      of Z3_PRINT_SMTLIB_FULL       => 0
       | Z3_PRINT_LOW_LEVEL         => 1
       | Z3_PRINT_SMTLIB_COMPLIANT  => 2
       | Z3_PRINT_SMTLIB2_COMPLIANT => 3
end

structure Z3_error_code = struct
  datatype t = Z3_OK
             | Z3_SORT_ERROR
             | Z3_IOB
             | Z3_INVALID_ARG
             | Z3_PARSER_ERROR
             | Z3_NO_PARSER
             | Z3_INVALID_PATTERN
             | Z3_MEMOUT_FAIL
             | Z3_FILE_ACCESS_ERROR
             | Z3_INTERNAL_FATAL
             | Z3_INVALID_USAGE
             | Z3_DEC_REF_ERROR
             | Z3_EXCEPTION

  fun fromInt n =
    case n
      of 0 => Z3_OK
       | 1 => Z3_SORT_ERROR
       | 2 => Z3_IOB
       | 3 => Z3_INVALID_ARG
       | 4 => Z3_PARSER_ERROR
       | 5 => Z3_NO_PARSER
       | 6 => Z3_INVALID_PATTERN
       | 7 => Z3_MEMOUT_FAIL
       | 8 => Z3_FILE_ACCESS_ERROR
       | 9 => Z3_INTERNAL_FATAL
       | 10 => Z3_INVALID_USAGE
       | 11 => Z3_DEC_REF_ERROR
       | 12 => Z3_EXCEPTION
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt e =
    case e
      of Z3_OK                => 0
       | Z3_SORT_ERROR        => 1
       | Z3_IOB               => 2
       | Z3_INVALID_ARG       => 3
       | Z3_PARSER_ERROR      => 4
       | Z3_NO_PARSER         => 5
       | Z3_INVALID_PATTERN   => 6
       | Z3_MEMOUT_FAIL       => 7
       | Z3_FILE_ACCESS_ERROR => 8
       | Z3_INTERNAL_FATAL    => 9
       | Z3_INVALID_USAGE     => 10
       | Z3_DEC_REF_ERROR     => 11
       | Z3_EXCEPTION         => 12
end

structure Z3_goal_prec = struct
  datatype t = Z3_GOAL_PRECISE
             | Z3_GOAL_UNDER
             | Z3_GOAL_OVER
             | Z3_GOAL_UNDER_OVER

  fun fromInt n =
    case n
      of 0 => Z3_GOAL_PRECISE
       | 1 => Z3_GOAL_UNDER
       | 2 => Z3_GOAL_OVER
       | 3 => Z3_GOAL_UNDER_OVER
       | n => raise Z3_DomainError.EnumDomain n

  fun toInt n =
    case n
      of Z3_GOAL_PRECISE    => 0
       | Z3_GOAL_UNDER      => 1
       | Z3_GOAL_OVER       => 2
       | Z3_GOAL_UNDER_OVER => 3
end

