
structure Z3_Quantifier =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3
in
  type Z3_context = unit ptr
  type Z3_pattern = unit ptr
  type Z3_sort    = unit ptr
  type Z3_ast     = unit ptr
  type Z3_app     = unit ptr
  type Z3_symbol  = unit ptr
  type Z3_bool    = int

  fun Z3_mk_pattern (c, args) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_pattern"))
    ( c : Z3_context
    , Vector.length args : int
    , args : Z3_ast vector) : Z3_pattern

  val Z3_mk_bound =
    Dyn.dlsym(libz3, "Z3_mk_bound")
    : _import (Z3_context, word, Z3_sort) -> Z3_ast

  fun Z3_mk_forall (c, weight, patterns, sorts, decl_names, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_forall"))
    ( c : Z3_context
    , weight : word
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , Vector.length sorts : int, sorts : Z3_sort vector
    , decl_names : Z3_symbol vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_exists (c, weight, patterns, sorts, decl_names, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_exists"))
    ( c : Z3_context
    , weight : word
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , Vector.length sorts : int, sorts : Z3_sort vector
    , decl_names : Z3_symbol vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_quantifier (c, is_forall, weight, patterns, sorts, decl_names, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_quantifier"))
    ( c : Z3_context
    , is_forall : Z3_bool
    , weight : word
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , Vector.length sorts : int, sorts : Z3_sort vector
    , decl_names : Z3_symbol vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_quantifier_ex (c, is_forall, weight, quantifier_id, skolem_id
                        , patterns, no_patterns, sorts, decl_names, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_quantifier_ex"))
    ( c : Z3_context
    , is_forall : Z3_bool
    , weight : word
    , quantifier_id : Z3_symbol
    , skolem_id : Z3_symbol
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , Vector.length no_patterns : int, no_patterns : Z3_ast vector
    , Vector.length sorts : int, sorts : Z3_sort vector
    , decl_names : Z3_symbol vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_forall_const (c, weight, bound, patterns, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_forall_const"))
    ( c : Z3_context
    , weight : word
    , Vector.length bound : int, bound : Z3_app vector
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_exists_const (c, weight, bound, patterns, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_exists_const"))
    ( c : Z3_context
    , weight : word
    , Vector.length bound : int, bound : Z3_app vector
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_quantifier_const (c, is_forall, weight
                            , bound, patterns, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_quantifier_const"))
    ( c : Z3_context
    , is_forall : Z3_bool
    , weight : word
    , Vector.length bound : int, bound : Z3_app vector
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , body : Z3_ast) : Z3_ast

  fun Z3_mk_quantifier_const_ex (c, is_forall, weight, quantifier_id, skolem_id
                                , bound, patterns, no_patterns, body) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_mk_quantifier_const_ex"))
    ( c : Z3_context
    , is_forall : Z3_bool
    , weight : word
    , quantifier_id : Z3_symbol
    , skolem_id : Z3_symbol
    , Vector.length bound : int, bound : Z3_app vector
    , Vector.length patterns : int, patterns : Z3_pattern vector
    , Vector.length no_patterns : int, no_patterns : Z3_ast vector
    , body : Z3_ast) : Z3_ast

end (* local *)
end

