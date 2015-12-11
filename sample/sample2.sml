
structure Main =
struct
local
  structure Ptr = Pointer
  structure D = Z3.Deprecated
  open Z3

  fun using get release during =
    let
      val resource = get ()
      val result = during resource handle exn => (release resource; raise exn)
    in
      result before release resource
    end

  fun with_config f =
    using Z3_mk_config
          Z3_del_config
          f

  fun mk_context () =
    with_config (fn cfg =>
      let
        val () = Z3_set_param_value (cfg, "model", "true")
        val ctx = Z3_mk_context cfg
      in
        Z3_set_error_handler(ctx, SOME (fn _ => print "error\n"));
        ctx
      end)

  fun with_context f =
    using mk_context
          Z3_del_context
          f

  fun local_ctx ctx f =
    using (fn () => (D.Z3_push ctx; ctx))
          (fn ctx' => D.Z3_pop (ctx', 0w1))
          f

  exception Unexpected of string

  fun prove ctx f is_valid =
    local_ctx ctx (fn ctx =>
    let
      val not_f = Z3_mk_not (ctx, f)
      val () = D.Z3_assert_cnstr (ctx, not_f)
      val m : Z3_model ref = ref (Ptr.NULL())
      val ret = D.Z3_check_and_get_model (ctx, m)
      val ref m = m
    in
      case ret
        of Z3_lbool.Z3_L_FALSE =>
              (print "valid\n";
               if not is_valid then raise Unexpected "prove/valid" else ())
         | Z3_lbool.Z3_L_UNDEF =>
              (print "unknown\n";
               if not (Ptr.isNull m)
               then print(concat["potential counterexample:\n"
                                , Z3_model_to_string (ctx, m), "\n"])
               else ();
               if is_valid then raise Unexpected "prove/unknown" else ())
         | Z3_lbool.Z3_L_TRUE =>
              (print "invalid\n";
               if not (Ptr.isNull m)
               then print(concat["counterexample:\n"
                                , Z3_model_to_string (ctx, m), "\n"])
               else ();
               if is_valid then raise Unexpected "prove/invalid" else ());
      if Ptr.isNull m
      then D.Z3_del_model (ctx, m)
      else ()
    end)
in
  fun go () =
     with_context (fn ctx =>
     let
       infix 4 ==
       fun p == q = Z3_mk_eq (ctx, p, q)

       infix 8 $
       fun f $ x = Z3_mk_app (ctx, f, Vector.fromList [x])

       (* create uninterpreted type *)
       val U = Z3_mk_uninterpreted_sort (ctx, Z3_mk_string_symbol (ctx, "U"))
       (* g : U -> U *)
       val g = Z3_mk_func_decl (ctx, Z3_mk_string_symbol (ctx, "g"), Vector.fromList[U], U)
       (* create x and y *)
       val x = Z3_mk_const (ctx, Z3_mk_string_symbol(ctx, "x"), U)
       val y = Z3_mk_const (ctx, Z3_mk_string_symbol(ctx, "y"), U)
     in
       D.Z3_assert_cnstr (ctx, x == y); (* assert x = y *)
       print "prove: x = y implies g(x) = g(y)\n";
       prove ctx (g $ x == g $ y) Z3_TRUE;
       print "disprove: x = y implies g(g(x)) = g(y)\n";
       prove ctx (g $ (g $ x) == g $ y) Z3_FALSE
     end)

  fun main (name, args) =
    (go();
     OS.Process.success
    )
end (* local *)
end
val _ = Main.main (CommandLine.name(), CommandLine.arguments())

