
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
    let val ty = Z3.Z3_mk_int_sort ctx
    in var ctx name ty
    end

  fun bool_var ctx name =
    let val ty = Z3.Z3_mk_bool_sort ctx
    in var ctx name ty
    end

  fun int ctx v =
    let val ty = Z3.Z3_mk_int_sort ctx
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

  fun main (name, args) =
    (display_version();
     simple_example();
     tutorial_sample();
     find_model_example1();
     find_model_example2()
     )
end
val _ =  Main.main (CommandLine.name(), CommandLine.arguments())

