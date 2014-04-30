
structure Z3_BitVector =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Dyn.dlopen "libz3.so"
in
  type Z3_context = unit ptr
  type Z3_ast     = unit ptr
  type Z3_bool    = int

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

end (* local *)
end

