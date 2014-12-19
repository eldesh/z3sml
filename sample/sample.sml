
structure Main =
struct
  structure Ptr = Pointer
  structure D = Z3.Deprecated
  structure Prop = Z3.Propositional

  fun var ctx name ty =
    let val sym = Z3.Z3_mk_string_symbol (ctx, name)
    in Z3.Z3_mk_const (ctx, sym, ty)
    end

  fun int_var ctx name =
    let val ty = Z3.Sort.Z3_mk_int_sort ctx
    in var ctx name ty
    end

  fun bool_var ctx name =
    let val ty = Z3.Sort.Z3_mk_bool_sort ctx
    in var ctx name ty
    end

  fun int ctx v =
    let val ty = Z3.Sort.Z3_mk_int_sort ctx
    in Z3.Z3_mk_int (ctx, v, ty)
    end

  fun check ctx expected =
    let
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val result = D.Z3_check_and_get_model (ctx, m)
      val () =
        if result=Z3.Z3_L_FALSE
        then print "unsat\n"
        else if result=Z3.Z3_L_UNDEF
        then (print "unknown\n";
              print (concat["potential model:\n"
                           , Z3.Z3_model_to_string (ctx, !m)
                           , "\n"]))
        else if result=Z3.Z3_L_TRUE
        then (print (concat["sat\n"
                           , Z3.Z3_model_to_string (ctx, !m)
                           , "\n"]))
        else ()
    in
      if !m <> Ptr.NULL() then D.Z3_del_model (ctx, !m) else ();
      if result <> expected then raise Fail "unexpected result" else ()
    end

  fun with_config f =
    let
      val cfg = Z3.Config.Z3_mk_config ()
      val r = f cfg
      val () = Z3.Config.Z3_del_config cfg
    in
      r
    end

  fun with_context f =
    with_config (fn cfg =>
    let
      val () = Z3.Config.Z3_set_param_value (cfg, "MODEL", "true")
      val ctx = Z3.Context.Z3_mk_context cfg
      val () = Z3.Z3_set_error_handler(ctx, fn _ => print "error\n")
      val r   = f ctx
      val ()  = Z3.Context.Z3_del_context ctx
    in
      r
    end)

  fun lbool_to_string x =
    if x=Z3.Z3_L_FALSE then "L_FALSE"
    else if x=Z3.Z3_L_UNDEF then "L_UNDEF"
    else if x=Z3.Z3_L_TRUE  then "L_TRUE"
    else raise Fail "lbool_to_string"

  fun simple_example () =
    with_context (fn ctx =>
    let val x = D.Z3_check ctx in
      print (concat["check:", lbool_to_string x, "\n"]);
      print (concat["CONTEXT:\n"
                   , D.Z3_context_to_string ctx
                   , "END OF CONTEXT\n"])
    end)

  fun demorgan () =
    with_context (fn ctx =>
    let
      val ()        = print "demorgan\n"
      val bool_sort = Z3.Sort.Z3_mk_bool_sort ctx
      val symbol_x  = Z3.Z3_mk_int_symbol (ctx, 0)
      val symbol_y  = Z3.Z3_mk_int_symbol (ctx, 1)
      val x         = Z3.Z3_mk_const (ctx, symbol_x, bool_sort)
      val y         = Z3.Z3_mk_const (ctx, symbol_y, bool_sort)
      val not_x     = Prop.Z3_mk_not (ctx, x)
      val not_y     = Prop.Z3_mk_not (ctx, y)
      (*
       * De Morgan - with a negation around
       * !(!(x && y) <-> (!x || !y))
       *)
      val args    = Array.fromList [x, y]
      val x_and_y = Prop.Z3_mk_and (ctx, 0w2, Array.vector args)
      val ls      = Prop.Z3_mk_not (ctx, x_and_y)
      val () = Array.update (args, 0, not_x)
      val () = Array.update (args, 1, not_y)
      val rs                 = Prop.Z3_mk_or (ctx, 0w2, Array.vector args)
      val conjecture         = Prop.Z3_mk_iff(ctx, ls, rs)
      val negated_conjecture = Prop.Z3_mk_not(ctx, conjecture)
      val () = D.Z3_assert_cnstr (ctx, negated_conjecture)
      val smt = D.Z3_check ctx
    in
           if smt = Z3.Z3_L_FALSE then print "DeMorgan is valid\n"
      else if smt = Z3.Z3_L_TRUE  then print "Undef\n"
      else if smt = Z3.Z3_L_UNDEF then print "DeMorgan is not valid\n"
      else raise Fail "Sample DeMorgan"
    end)

  fun find_model_example1 () =
    with_context (fn ctx =>
    let
      val x = bool_var ctx "x"
      val y = bool_var ctx "y"
      val x_xor_y = Prop.Z3_mk_xor (ctx, x, y)
      val () = D.Z3_assert_cnstr (ctx, x_xor_y)
    in
      check ctx Z3.Z3_L_TRUE
    end)

  fun find_model_example2 () =
    let
      open Z3.Arithmetic
      val () = print "find_model_example2\n"
      val cfg = Z3.Config.Z3_mk_config ()
      val ctx = Z3.Context.Z3_mk_context cfg

      val x = int_var ctx "x"
      val y = int_var ctx "y"
      val one = int ctx 1
      val two = int ctx 2

      val y_plus_one = Z3.Arithmetic.Z3_mk_add (ctx, 0w2, Vector.fromList [y, one])

      val c1 = Z3_mk_lt (ctx, x, y_plus_one)
      val c2 = Z3_mk_gt (ctx, x, two)

      val () = D.Z3_assert_cnstr (ctx, c1)
      val () = D.Z3_assert_cnstr (ctx, c2)

      val () = print "model for: x < y + 1, x > 2\n"
      val () = check ctx Z3.Z3_L_TRUE

      val x_eq_y = Prop.Z3_mk_eq (ctx, x, y)
      val c3     = Prop.Z3_mk_not(ctx, x_eq_y)
    in
      D.Z3_assert_cnstr (ctx, c3);
      print "model for: x < y + 1, x > 2, not(x = y)\n";
      check ctx Z3.Z3_L_TRUE;
      Z3.Context.Z3_del_context ctx
    end

  fun mk_context () =
    let
      val cfg = Z3.Config.Z3_mk_config ()
      val () = Z3.Config.Z3_set_param_value (cfg, "MODEL", "true");
    in
      let
        val ctx = Z3.Context.Z3_mk_context cfg
      in
        Z3.Z3_set_error_handler (ctx, fn _=> print "error\n");
        Z3.Config.Z3_del_config cfg;
        ctx
      end
    end

  fun display_version () =
    let
      val (major, minor, build, revision) = (ref 0w0, ref 0w0, ref 0w0, ref 0w0)
      val word = Word.toString
    in
      Z3.Z3_get_version (major, minor, build, revision);
      print (concat["Z3 "
            , String.concatWith
                 "." [word (!major), word (!minor), word (!build), word (!revision)]
            , "\n"])
    end

  fun tutorial_sample () =
    with_context (fn ctx =>
    let
      open Z3.Arithmetic
      val solver = Z3.Solver.Z3_mk_solver ctx
      val x = int_var ctx "x"
      val y = int_var ctx "y"
      val two   = int ctx 2
      val seven = int ctx 7
      val ten   = int ctx 10
      fun add ctx (l,r) = Z3_mk_add (ctx, 0w2, Vector.fromList [l, r])
      fun mul ctx (l,r) = Z3_mk_mul (ctx, 0w2, Vector.fromList [l, r])
      val () = app (fn assert => Z3.Solver.Z3_solver_assert (ctx, solver, assert))
                    [ Z3_mk_gt (ctx, x, two) (* x < 2 *)
                    , Z3_mk_lt (ctx, y, ten) (* y < 10 *)
                    , Prop.Z3_mk_eq (ctx, add ctx (x, mul ctx (two, y))
                                   , seven) (* x + 2*y = 7 *)
                    ]
      val () = print (Z3.Solver.Z3_solver_to_string (ctx, solver) ^ "\n")
      val model =
        let
          val v = Z3.Solver.Z3_solver_check (ctx, solver)
        in
          if v=Z3.Z3_L_TRUE
          then Z3.Solver.Z3_solver_get_model (ctx, solver)
          else raise Fail "solver_check"
        end
      val decls = Vector.tabulate(
                      Word.toInt (Z3.Model.Z3_model_get_num_consts(ctx, model))
                    , fn i=> Z3.Model.Z3_model_get_const_decl(ctx, model, Word.fromInt i))
    in
      (*
      print (Z3.Z3_model_to_string (ctx, model)^"\n");
      *)
      Vector.app
         (fn decl =>
          let
            val ast = Z3.Model.Z3_model_get_const_interp (ctx, model, decl)
          in
            print (concat[Z3.Z3_func_decl_to_string (ctx, decl)
                         , " -> "
                         ,Z3.Z3_ast_to_string (ctx, ast)
                         , "\n"])
          end)
         decls
    end)

  fun mk_unary_app ctx f x =
    let
      val args = Vector.fromList [x]
    in
      Z3.Z3_mk_app (ctx, f, 0w1, args)
    end

  fun using get release f =
    let
      val resource = get ()
      val r = f resource handle exn => (release resource; raise exn)
      val () = release resource
    in r
    end

  fun local_ctx ctx f =
    using (fn () => (D.Z3_push ctx; ctx))
          (fn ctx' => D.Z3_pop (ctx', 0w1))
          f

  exception Unexpected of string

  fun prove ctx f is_valid =
    local_ctx ctx (fn ctx =>
    let
      val is_valid = is_valid = Z3.Z3_TRUE
      val not_f = Prop.Z3_mk_not (ctx, f)
      val () = D.Z3_assert_cnstr (ctx, not_f)
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val ret = D.Z3_check_and_get_model (ctx, m)
    in
      using (fn()=> m) (fn m=> if not (Ptr.isNull (!m))
                               then D.Z3_del_model (ctx, !m)
                               else ())
      (fn ref m =>
        if ret = Z3.Z3_L_FALSE
        then
          (print "valid\n";
           if not is_valid then raise Unexpected "prove/valid" else ())
        else if ret = Z3.Z3_L_UNDEF
        then
          (print "unknown\n";
           if not (Ptr.isNull m)
           then print(concat["potential counterexample:\n"
                            , Z3.Z3_model_to_string (ctx, m), "\n"])
           else ();
           if is_valid then raise Unexpected "prove/unknown" else ())
        else if ret = Z3.Z3_L_TRUE
        then
          (print "invalid\n";
           if not (Ptr.isNull m)
           then print(concat["counterexample:\n"
                            , Z3.Z3_model_to_string (ctx, m), "\n"])
           else ();
           if is_valid then raise Unexpected "prove/invalid" else ())
        else ())
    end)

  fun prove_example1() =
    (print "\nprove_example1\n";
     with_context (fn ctx =>
     let
       (* create uninterpreted type *)
       val U_name   = Z3.Z3_mk_string_symbol (ctx, "U")
       val U        = Z3.Sort.Z3_mk_uninterpreted_sort (ctx, U_name)
       (* declare function g *)
       val g_name   = Z3.Z3_mk_string_symbol (ctx, "g")
       val g_domain = Vector.fromList [U]
       val g        = Z3.Z3_mk_func_decl (ctx, g_name, 0w1, g_domain, U)
       (* create x and y *)
       val x_name   = Z3.Z3_mk_string_symbol (ctx, "x")
       val y_name   = Z3.Z3_mk_string_symbol (ctx, "y")
       val x        = Z3.Z3_mk_const (ctx, x_name, U)
       val y        = Z3.Z3_mk_const (ctx, y_name, U)
       (* create g(x), g(y) *)
       val gx       = mk_unary_app ctx g x
       val gy       = mk_unary_app ctx g y
       (* assert x = y *)
       val ()  = D.Z3_assert_cnstr (ctx, Prop.Z3_mk_eq (ctx, x, y))
       (* prove g(x) = g(y) *)
       val f   = Prop.Z3_mk_eq (ctx, gx, gy)
       val ()  = print "prove: x = y implies g(x) = g(y)\n"
       val ()  = prove ctx f Z3.Z3_TRUE
       (* create g(g(x)) *)
       val ggx = mk_unary_app ctx g gx
       (* disprove g(g(x)) = g(y) *)
       val f   = Prop.Z3_mk_eq (ctx, ggx, gy)
       val ()  = print "disprove: x = y implies g(g(x)) = g(y)\n"
       val ()  = prove ctx f Z3.Z3_FALSE
     in
       ()
     end))

  fun main (name, args) =
    (display_version();
     simple_example();
     demorgan();
     find_model_example1();
     find_model_example2();
     prove_example1();
     tutorial_sample()
     )
end
val _ =  Main.main (CommandLine.name(), CommandLine.arguments())

