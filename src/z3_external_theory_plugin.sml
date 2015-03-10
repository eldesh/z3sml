
structure Z3_ExternalTheoryPlugin =
struct
local
  structure Ptr = Pointer
  structure Dyn = DynamicLink
  val libz3 = Library.libz3

  fun importVector p n =
    Vector.tabulate(n, fn i=>
      SMLSharp_Builtin.Pointer.deref (Pointer.advance(p, i)))
in
  type Z3_context     = unit ptr
  type Z3_theory      = unit ptr
  type Z3_theory_data = unit ptr
  type Z3_symbol      = unit ptr
  type Z3_sort        = unit ptr
  type Z3_ast         = unit ptr
  type Z3_func_decl   = unit ptr

  type Z3_string = String.string
  type Z3_bool   = Z3_bool.t

  type Z3_reduce_app_callback_fptr =
         (Z3_theory * Z3_func_decl * Z3_ast vector * Z3_ast ref) -> Z3_bool

  type Z3_reduce_eq_callback_fptr =
         (Z3_theory * Z3_ast * Z3_ast * Z3_ast ref) -> Z3_bool

  type Z3_reduce_distinct_callback_fptr =
         (Z3_theory * Z3_ast vector * Z3_ast ref ) -> Z3_bool

  val Z3_mk_theory =
    Dyn.dlsym(libz3, "Z3_mk_theory")
    : _import (Z3_context, Z3_string, Z3_theory_data) -> Z3_theory

  val Z3_theory_get_ext_data =
    Dyn.dlsym(libz3, "Z3_theory_get_ext_data")
    : _import Z3_theory -> Z3_theory_data

  val Z3_theory_mk_sort =
    Dyn.dlsym(libz3, "Z3_theory_mk_sort")
    : _import (Z3_context, Z3_theory, Z3_symbol) -> Z3_sort

  val Z3_theory_mk_value =
    Dyn.dlsym(libz3, "Z3_theory_mk_value")
    : _import (Z3_context, Z3_theory, Z3_symbol, Z3_sort) -> Z3_ast

  val Z3_theory_mk_constant =
    Dyn.dlsym(libz3, "Z3_theory_mk_constant")
    : _import (Z3_context, Z3_theory, Z3_symbol, Z3_sort) -> Z3_ast

  fun Z3_theory_mk_func_decl (c, t, n, domain, range) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_theory_mk_func_decl"))
    ( c : Z3_context
    , t : Z3_theory
    , n : Z3_symbol
    , Vector.length domain : int
    , domain : Z3_sort vector
    , range : Z3_sort) : Z3_func_decl

  val Z3_theory_get_context =
    Dyn.dlsym(libz3, "Z3_theory_get_context")
    : _import Z3_theory -> Z3_context

  val Z3_set_delete_callback =
    Dyn.dlsym(libz3, "Z3_set_delete_callback")
    : _import (Z3_theory, Z3_theory->()) -> ()

  val Z3_set_reduce_app_callback_raw =
    Dyn.dlsym(libz3, "Z3_set_reduce_app_callback")
    : _import (Z3_theory
                , (Z3_theory, Z3_func_decl, word, Z3_ast ptr, Z3_ast ptr) -> int) -> ()

  fun Z3_set_reduce_app_callback (t, f) =
    let
      fun f' (t, d, n, args, r) =
        let
          val args = importVector args (Word.toInt n)
          val r'   = ref (SMLSharp_Builtin.Pointer.deref r)
        in
          Z3_bool.toInt (f (t, d, args, r'))
        end
    in Z3_set_reduce_app_callback_raw (t, f')
    end

  val Z3_set_reduce_distinct_callback_raw =
    Dyn.dlsym(libz3, "Z3_set_reduce_distinct_callback")
    : _import (Z3_theory, (Z3_theory, word, Z3_ast ptr, Z3_ast ptr) -> int) -> ()

  fun Z3_set_reduce_distinct_callback (t, f) =
    let
      fun f' (t, n, args, r) =
        let
          val args = importVector args (Word.toInt n)
          val r' = ref (SMLSharp_Builtin.Pointer.deref r)
        in Z3_bool.toInt (f (t, args, r'))
        end
    in Z3_set_reduce_distinct_callback_raw (t, f')
    end

  val Z3_set_reduce_eq_callback_raw =
    Dyn.dlsym(libz3, "Z3_set_reduce_eq_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast, Z3_ast, Z3_ast ptr) -> int) -> ()

  fun Z3_set_reduce_eq_callback (t, f) =
    let
      fun f' (t, s_1, s_2, r) =
        let val r' = ref (SMLSharp_Builtin.Pointer.deref r)
        in Z3_bool.toInt (f (t, s_1, s_2, r'))
        end
    in Z3_set_reduce_eq_callback_raw (t, f')
    end

  val Z3_set_new_app_callback =
    Dyn.dlsym(libz3, "Z3_set_new_app_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast)->()) -> ()

  val Z3_set_new_elem_callback =
    Dyn.dlsym(libz3, "Z3_set_new_elem_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast)->()) -> ()

  val Z3_set_init_search_callback =
    Dyn.dlsym(libz3, "Z3_set_init_search_callback")
    : _import (Z3_theory, Z3_theory -> ()) -> ()

  val Z3_set_push_callback =
    Dyn.dlsym(libz3, "Z3_set_push_callback")
    : _import (Z3_theory, Z3_theory -> ()) -> ()

  val Z3_set_pop_callback =
    Dyn.dlsym(libz3, "Z3_set_pop_callback")
    : _import (Z3_theory, Z3_theory -> ()) -> ()

  val Z3_set_restart_callback =
    Dyn.dlsym(libz3, "Z3_set_restart_callback")
    : _import (Z3_theory, Z3_theory -> ()) -> ()

  val Z3_set_reset_callback =
    Dyn.dlsym(libz3, "Z3_set_reset_callback")
    : _import (Z3_theory, Z3_theory -> ()) -> ()

  val Z3_set_final_check_callback_raw =
    Dyn.dlsym(libz3, "Z3_set_final_check_callback")
    : _import (Z3_theory, Z3_theory -> int) -> ()

  fun Z3_set_final_check_callback (t, f) =
    let fun f' t = Z3_bool.toInt (f t) in
      Z3_set_final_check_callback_raw (t, f')
    end

  val Z3_set_new_eq_callback =
    Dyn.dlsym(libz3, "Z3_set_new_eq_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast, Z3_ast)->()) -> ()

  val Z3_set_new_diseq_callback =
    Dyn.dlsym(libz3, "Z3_set_new_diseq_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast, Z3_ast)->()) -> ()

  val Z3_set_new_assignment_callback_raw =
    Dyn.dlsym(libz3, "Z3_set_new_assignment_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast, int)->()) -> ()

  fun Z3_set_new_assignment_callback (t, f) =
    let fun f' (t, p, v) = f (t, p, Z3_bool.fromInt v) in
      Z3_set_new_assignment_callback_raw (t, f')
    end

  val Z3_set_new_relevant_callback =
    Dyn.dlsym(libz3, "Z3_set_new_relevant_callback")
    : _import (Z3_theory, (Z3_theory, Z3_ast) -> ()) -> ()

  val Z3_theory_assert_axiom =
    Dyn.dlsym(libz3, "Z3_theory_assert_axiom")
    : _import (Z3_theory, Z3_ast) -> ()

  val Z3_theory_assume_eq =
    Dyn.dlsym(libz3, "Z3_theory_assume_eq")
    : _import (Z3_theory, Z3_ast, Z3_ast) -> ()

  fun Z3_theory_enable_axiom_simplification (t, flag) =
    _ffiapply (Dyn.dlsym(libz3, "Z3_theory_enable_axiom_simplification"))
    ( t : Z3_theory
    , Z3_bool.toInt flag : int) : ()

  val Z3_theory_get_eqc_root =
    Dyn.dlsym(libz3, "Z3_theory_get_eqc_root")
    : _import (Z3_theory, Z3_ast) -> Z3_ast

  val Z3_theory_get_eqc_next =
    Dyn.dlsym(libz3, "Z3_theory_get_eqc_next")
    : _import (Z3_theory, Z3_ast) -> Z3_ast

  val Z3_theory_get_num_parents =
    Dyn.dlsym(libz3, "Z3_theory_get_num_parents")
    : _import (Z3_theory, Z3_ast) -> word

  val Z3_theory_get_parent =
    Dyn.dlsym(libz3, "Z3_theory_get_parent")
    : _import (Z3_theory, Z3_ast, word) -> Z3_ast

  val Z3_theory_is_value =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_theory_is_value")
       : _import (Z3_theory, Z3_ast) -> int)

  val Z3_theory_is_decl =
    Z3_bool.fromInt o
      (Dyn.dlsym(libz3, "Z3_theory_is_decl")
       : _import (Z3_theory, Z3_func_decl) -> int)

  val Z3_theory_get_num_elems =
    Dyn.dlsym(libz3, "Z3_theory_get_num_elems")
    : _import Z3_theory -> word

  val Z3_theory_get_elem =
    Dyn.dlsym(libz3, "Z3_theory_get_elem")
    : _import (Z3_theory, word) -> Z3_ast

  val Z3_theory_get_num_apps =
    Dyn.dlsym(libz3, "Z3_theory_get_num_apps")
    : _import Z3_theory -> word

  val Z3_theory_get_app =
    Dyn.dlsym(libz3, "Z3_theory_get_app")
    : _import (Z3_theory, word) -> Z3_ast

end (* local *)
end

