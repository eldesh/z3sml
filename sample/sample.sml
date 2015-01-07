
structure Main =
struct
  structure Ptr = Pointer
  structure D = Z3.Deprecated
  structure Prop = Z3.Propositional
  structure E = Z3.Enum

  fun for v inv next f =
    if inv v
    then (f v; for (next v) inv next f)
    else ()

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
    in Z3.Numerals.Z3_mk_int (ctx, v, ty)
    end

  fun check ctx expected =
    let
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val result = D.Z3_check_and_get_model (ctx, m)
      val () =
        if result = E.Z3_L_FALSE
        then print "unsat\n"
        else if result = E.Z3_L_UNDEF
        then (print "unknown\n";
              print (concat["potential model:\n"
                           , Z3.Stringconv.Z3_model_to_string (ctx, !m)
                           , "\n"]))
        else if result = E.Z3_L_TRUE
        then (print (concat["sat\n"
                           , Z3.Stringconv.Z3_model_to_string (ctx, !m)
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
    let
      val ctx = with_config
                  (fn cfg =>
                    (Z3.Config.Z3_set_param_value (cfg, "model", "true");
                     let val ctx = Z3.Context.Z3_mk_context cfg in
                       Z3.Error.Z3_set_error_handler(ctx, fn _ => print "error\n");
                       ctx
                     end))
      val r   = f ctx
      val ()  = Z3.Context.Z3_del_context ctx
    in
      r
    end

  fun lbool_to_string x =
         if x = E.Z3_L_FALSE then "L_FALSE"
    else if x = E.Z3_L_UNDEF then "L_UNDEF"
    else if x = E.Z3_L_TRUE  then "L_TRUE"
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
      val x_and_y = Prop.Z3_mk_and (ctx, Array.vector args)
      val ls      = Prop.Z3_mk_not (ctx, x_and_y)
      val () = Array.update (args, 0, not_x)
      val () = Array.update (args, 1, not_y)
      val rs                 = Prop.Z3_mk_or (ctx, Array.vector args)
      val conjecture         = Prop.Z3_mk_iff(ctx, ls, rs)
      val negated_conjecture = Prop.Z3_mk_not(ctx, conjecture)
      val () = D.Z3_assert_cnstr (ctx, negated_conjecture)
      val smt = D.Z3_check ctx
    in
           if smt = E.Z3_L_FALSE then print "DeMorgan is valid\n"
      else if smt = E.Z3_L_TRUE  then print "Undef\n"
      else if smt = E.Z3_L_UNDEF then print "DeMorgan is not valid\n"
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
      check ctx E.Z3_L_TRUE
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
      val () = check ctx E.Z3_L_TRUE

      val x_eq_y = Prop.Z3_mk_eq (ctx, x, y)
      val c3     = Prop.Z3_mk_not(ctx, x_eq_y)
    in
      D.Z3_assert_cnstr (ctx, c3);
      print "model for: x < y + 1, x > 2, not(x = y)\n";
      check ctx E.Z3_L_TRUE;
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
        Z3.Error.Z3_set_error_handler (ctx, fn _=> print "error\n");
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
          if v= E.Z3_L_TRUE
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
            print (concat[Z3.Stringconv.Z3_func_decl_to_string (ctx, decl)
                         , " -> "
                         ,Z3.Stringconv.Z3_ast_to_string (ctx, ast)
                         , "\n"])
          end)
         decls
    end)

  fun mk_unary_app ctx f x =
    let
      val args = Vector.fromList [x]
    in
      Z3.Z3_mk_app (ctx, f, args)
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
  exception Unreachable of string

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
        if ret = E.Z3_L_FALSE
        then
          (print "valid\n";
           if not is_valid then raise Unexpected "prove/valid" else ())
        else if ret = E.Z3_L_UNDEF
        then
          (print "unknown\n";
           if not (Ptr.isNull m)
           then print(concat["potential counterexample:\n"
                            , Z3.Stringconv.Z3_model_to_string (ctx, m), "\n"])
           else ();
           if is_valid then raise Unexpected "prove/unknown" else ())
        else if ret = E.Z3_L_TRUE
        then
          (print "invalid\n";
           if not (Ptr.isNull m)
           then print(concat["counterexample:\n"
                            , Z3.Stringconv.Z3_model_to_string (ctx, m), "\n"])
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
       val g        = Z3.Z3_mk_func_decl (ctx, g_name, g_domain, U)
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

  fun mk_var ctx name ty =
    Z3.Z3_mk_const (ctx, Z3.Z3_mk_string_symbol (ctx, name), ty)

  fun mk_int_var ctx name =
    mk_var ctx name (Z3.Sort.Z3_mk_int_sort ctx)

  fun mk_int ctx n =
    Z3.Numerals.Z3_mk_int (ctx, n, Z3.Sort.Z3_mk_int_sort ctx)

  fun prove_example2() =
    (print "\nprove_example2\n";
     with_context (fn ctx =>
     let
       (* declare function g *)
       val int_sort = Z3.Sort.Z3_mk_int_sort ctx
       val g_name   = Z3.Z3_mk_string_symbol (ctx, "g")
       val g_domain = Vector.fromList [int_sort]
       val g        = Z3.Z3_mk_func_decl (ctx, g_name, g_domain, int_sort)
       (* create x, y, and z *)
       val x        = mk_int_var ctx "x"
       val y        = mk_int_var ctx "y"
       val z        = mk_int_var ctx "z"
       (* create gx, gy, gz *)
       val gx       = mk_unary_app ctx g x
       val gy       = mk_unary_app ctx g y
       val gz       = mk_unary_app ctx g z
       (* create zero *)
       val zero     = mk_int ctx 0
       (* assert not(g(g(x) - g(y)) = g(z)) *)
       val args     = Vector.fromList [gx, gy]
       val gx_gy    = Z3.Arithmetic.Z3_mk_sub (ctx, 0w2, args)
       val ggx_gy   = mk_unary_app ctx g gx_gy
       val eq       = Prop.Z3_mk_eq  (ctx, ggx_gy, gz)
       val c1       = Prop.Z3_mk_not (ctx, eq)
       val () = D.Z3_assert_cnstr (ctx, c1)
       (* assert x + z <= y *)
       val args     = Vector.fromList [x,z]
       val x_plus_z = Z3.Arithmetic.Z3_mk_add (ctx, 0w2, args)
       val c2       = Z3.Arithmetic.Z3_mk_le (ctx, x_plus_z, y)
       val () = D.Z3_assert_cnstr (ctx, c2)
       (* assert y <= x *)
       val c3       = Z3.Arithmetic.Z3_mk_le (ctx, y, x)
       val () = D.Z3_assert_cnstr (ctx, c3)
     in
       (* prove z < 0 *)
       let
         val f = Z3.Arithmetic.Z3_mk_lt (ctx, z, zero)
       in
         print "prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n";
         prove ctx f Z3.Z3_TRUE
       end;
       (* disprove z < ~1 *)
       let
         val minus_one = mk_int ctx ~1
         val f = Z3.Arithmetic.Z3_mk_lt (ctx, z, minus_one)
       in
         print "disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n";
         prove ctx f Z3.Z3_FALSE
       end
     end))

  structure Display =
  struct
    fun symbol c out s =
      let
        val kind = Z3.Accessor.Z3_get_symbol_kind (c, s)
      in
        if kind = E.Z3_INT_SYMBOL
        then
          TextIO.output (out, concat["#", Int.toString
                                         (Z3.Accessor.Z3_get_symbol_int(c, s))])
        else if kind = E.Z3_STRING_SYMBOL
        then
          TextIO.output (out, Z3.Accessor.Z3_get_symbol_string(c, s))
        else
          raise Unreachable "Display.symbol"
      end

    fun sort c out ty =
      let
        fun succ w = w + 0w1
        val printf = TextIO.output
        val kind = Z3.Accessor.Z3_get_sort_kind (c, ty)
      in
        if kind = E.Z3_UNINTERPRETED_SORT
        then symbol c out (Z3.Accessor.Z3_get_sort_name (c, ty))
        else if kind = E.Z3_BOOL_SORT
        then printf (out, "bool")
        else if kind = E.Z3_INT_SORT
        then printf (out, "int")
        else if kind = E.Z3_REAL_SORT
        then printf (out, "real")
        else if kind = E.Z3_BV_SORT
        then printf (out, concat["bv"
                          , Word.toString(Z3.Accessor.Z3_get_bv_sort_size(c,ty))])
        else if kind = E.Z3_ARRAY_SORT
        then
          (printf (out, "[");
           sort c out (Z3.Accessor.Z3_get_array_sort_domain(c, ty));
           printf (out, "->");
           sort c out (Z3.Accessor.Z3_get_array_sort_range (c, ty));
           printf (out, "]"))
        else if kind = E.Z3_DATATYPE_SORT
        then
          ((if Z3.Accessor.Z3_get_datatype_sort_num_constructors(c, ty) <> 0w1
            then printf (out, Z3.Stringconv.Z3_sort_to_string(c, ty))
            else ());
           printf (out, "(");
           for 0w0 (fn i=> i < Z3.Accessor.Z3_get_tuple_sort_num_fields(c, ty)) succ
           (fn i=>
             let
               val field = Z3.Accessor.Z3_get_tuple_sort_field_decl(c, ty, i)
             in
               (if i > 0w0 then printf (out, ", ") else ());
               sort c out (Z3.Accessor.Z3_get_range(c, field))
             end);
           printf (out, ")"))
        else
          (printf (out, "unknown[");
           symbol c out (Z3.Accessor.Z3_get_sort_name(c, ty));
           printf (out, "]");
           raise Fail "unknown")
      end

    fun ast c out v =
      let
        fun succ w = w + 0w1
        val kind = Z3.Accessor.Z3_get_ast_kind (c, v)
      in
        if kind = E.Z3_NUMERAL_AST
        then
          (TextIO.output (out, Z3.Accessor.Z3_get_numeral_string (c, v));
           TextIO.output (out, ":");
           sort c out (Z3.Accessor.Z3_get_sort (c, v)))
        else if kind = E.Z3_APP_AST
        then
          let
            val app = Z3.Accessor.Z3_to_app (c, v)
            val num_fields = Z3.Accessor.Z3_get_app_num_args (c, app)
            val d = Z3.Accessor.Z3_get_app_decl (c, app)
          in
            TextIO.output (out, Z3.Stringconv.Z3_func_decl_to_string(c, d));
            if num_fields > 0w0
            then
              (TextIO.output (out, "[");
               for 0w0 (fn i=> i < num_fields) succ (fn i=>
                 (if i > 0w0 then TextIO.output (out, ", ") else ();
                  ast c out (Z3.Accessor.Z3_get_app_arg (c, app, i))
                 )
               );
               TextIO.output (out, "]")
              )
            else
              ()
          end
        else if kind = E.Z3_QUANTIFIER_AST
        then
          TextIO.output (out, "quantifier")
        else
          TextIO.output (out, "#unknown")
      end

    fun function_interpretations c out m =
      let
        fun succ w = w + 0w1
      in
        TextIO.output(out, "function interpretations:\n");
        for 0w0 (fn i=> i < D.Z3_get_model_num_funcs(c, m)) succ
        (fn i=>
        let
          val fdecl = D.Z3_get_model_func_decl(c, m, i)
          val () = symbol c out (Z3.Accessor.Z3_get_decl_name(c, fdecl))
          val () = TextIO.output (out, " = {")
          val num_entries = D.Z3_get_model_func_num_entries(c, m, i)
        in
          for 0w0 (fn j=> j < num_entries) succ
          (fn j=>
           (if j > 0w0 then TextIO.output(out, ", ") else ();
            TextIO.output(out, "(");
            for 0w0 (fn k=> k < D.Z3_get_model_func_entry_num_args(c, m, i, j)) succ
            (fn k=>
             (if k > 0w0 then TextIO.output(out, ", ") else ();
              ast c out (D.Z3_get_model_func_entry_arg(c, m, i, j, k))
             )
            );
            TextIO.output(out, "|->");
            ast c out (D.Z3_get_model_func_entry_value(c, m, i, j));
            TextIO.output(out, ")")
           )
          );
          if num_entries > 0w0 then TextIO.output(out, ", ") else ();
          TextIO.output(out, "(else|->");
          ast c out (D.Z3_get_model_func_else(c, m, i));
          TextIO.output(out, ")]\n")
        end)
      end

    fun model ctx out m =
      let
        fun succ w = w + 0w1
        val num_constants = D.Z3_get_model_num_constants (ctx, m)
      in
        for 0w0 (fn i=> i<num_constants) succ (fn i=>
        let
          val cnst = D.Z3_get_model_constant (ctx, m, i)
          val name = Z3.Accessor.Z3_get_decl_name (ctx, cnst)
          val () = symbol ctx out name
          val () = TextIO.output (out, " = ")
          val a = Z3.Z3_mk_app (ctx, cnst, Vector.fromList[])
          val v = ref a
          val ok = D.Z3_eval (ctx, m, a, v)
        in
          ast ctx out (!v);
          TextIO.output (out, "\n")
        end);
        function_interpretations ctx out m
      end

  end (* Display *)

  fun check2 ctx expected_result =
    let
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val result = D.Z3_check_and_get_model (ctx, m)
    in
      if result = E.Z3_L_FALSE
      then
        print "unsat\n"
      else if result = E.Z3_L_UNDEF
      then
        (print "unknown\n";
         print "potential model:\n";
         Display.model ctx TextIO.stdOut (!m))
      else if result = E.Z3_L_TRUE
      then
        (print "sat\n";
         Display.model ctx TextIO.stdOut (!m))
      else ();
      if not (Ptr.isNull (!m))
      then D.Z3_del_model (ctx, !m) else ();
      if result <> expected_result
      then raise Unexpected "check2"
      else ()
    end

  fun mk_context_custom cfg error_handler =
    let
      val ()  = Z3.Config.Z3_set_param_value (cfg, "model", "true")
      val ctx = Z3.Context.Z3_mk_context cfg
      val ()  = Z3.Error.Z3_set_error_handler(ctx, error_handler)
    in
      ctx
    end

  fun assert_inj_axiom ctx f i =
    let
      val sz = Z3.Accessor.Z3_get_domain_size (ctx, f)
      val _  = if i >= sz then raise Fail "failed to create inj axiom"
               else ()
      val finv_domain = Z3.Accessor.Z3_get_range (ctx, f)
      val finv_range  = Z3.Accessor.Z3_get_domain(ctx, f, i)
      val finv        = Z3.Z3_mk_fresh_func_decl(ctx, "inv"
                            , Vector.fromList[finv_domain], finv_range)
      (* allocate temporary arrays *)
      val types = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Accessor.Z3_get_domain (ctx, f, Word.fromInt j))
      val names = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Z3_mk_int_symbol (ctx, j))
      val xs    = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Quantifier.Z3_mk_bound(ctx, Word.fromInt j, Vector.sub(types, j)))
      val x_i   = Vector.sub (xs, Word.toInt i)
      val fxs   = Z3.Z3_mk_app (ctx, f, xs)
      val finv_fxs = mk_unary_app ctx finv fxs
      val eq       = Prop.Z3_mk_eq (ctx, finv_fxs, x_i)
      val p        = Z3.Quantifier.Z3_mk_pattern(ctx
                                                , 0w1, Vector.fromList[fxs])
      val () = print(concat["pattern: ", Z3.Stringconv.Z3_pattern_to_string(ctx, p), "\n\n"])
      val q  = Z3.Quantifier.Z3_mk_forall (ctx, 0w0, 0w1, Vector.fromList[p], sz
                                            , types, names, eq)
    in
      print(concat["assert axiom:\n", Z3.Stringconv.Z3_ast_to_string(ctx, q), "\n"]);
      D.Z3_assert_cnstr(ctx, q)
    end

  fun quantifier_example1() =
    (print "\nquantifier_example1\n";
     let
       val ctx = with_config (fn cfg =>
                  (Z3.Global.Z3_global_param_set("smt.mbqi.max_iterations", "10");
                   mk_context_custom cfg (fn _ => print "error\n")
                  ))
       (* declare function f *)
       val int_sort = Z3.Sort.Z3_mk_int_sort ctx
       val f_name   = Z3.Z3_mk_string_symbol (ctx, "f")
       val f_domain = Vector.fromList [int_sort, int_sort]
       val f        = Z3.Z3_mk_func_decl(ctx, f_name, f_domain, int_sort)

       (* assert that f is injective in the second argument. *)
       val () = assert_inj_axiom ctx f 0w1
     in
       ()
     end)

  fun push_pop_example1 () =
    (print "\npush_pop_example1\n";
     with_context (fn ctx =>
     let
       (* create a big number *)
       val int_sort   = Z3.Sort.Z3_mk_int_sort ctx
       val big_number = Z3.Numerals.Z3_mk_numeral
                         (ctx, "1000000000000000000000000000000000000000000000000000000", int_sort)
       (* create number 3 *)
       val three      = Z3.Numerals.Z3_mk_numeral (ctx, "3", int_sort)
       (* create x *)
       val x_sym      = Z3.Z3_mk_string_symbol (ctx, "x")
       val x          = Z3.Z3_mk_const (ctx, x_sym, int_sort)
       (* assert x >= "big number" *)
       val c1         = Z3.Arithmetic.Z3_mk_ge (ctx, x, big_number)
       val ()         = print "assert: x >= 'big number'\n"
       val ()         = D.Z3_assert_cnstr (ctx, c1)
       (* create a backtracking point *)
       val ()         = print "push\n"
     in
       local_ctx ctx (fn ctx =>
       let
         val () = print (concat["number of scopes: "
                               , Word.toString (D.Z3_get_num_scopes ctx)
                               , "\n"])
         val c2 = Z3.Arithmetic.Z3_mk_le (ctx, x, three)
         val () = print "assert: x <= 3\n"
         val () = D.Z3_assert_cnstr (ctx, c2)
       in
         (* context is inconsistent at this point *)
         check2 ctx E.Z3_L_FALSE;
         (* backtrack: the constraint x <= 3 will be removed, since it was
          * asserted after the last Z3_push. *)
         print "pop\n"
       end);
       print (concat["number of scopes: "
            , Word.toString (D.Z3_get_num_scopes ctx), "\n"]);
       (* the context is consistent again. *)
       check2 ctx E.Z3_L_TRUE;

       (* new constraints can be asserted... *)
       let
         (* create y *)
         val y_sym = Z3.Z3_mk_string_symbol (ctx, "y")
         val y     = Z3.Z3_mk_const (ctx, y_sym, int_sort)
         (* assert y > x *)
         val c3    = Z3.Arithmetic.Z3_mk_gt(ctx, y, x)
       in
         print "assert: y > x\n";
         D.Z3_assert_cnstr(ctx, c3);
         (* the context is still consistent *)
         check2 ctx E.Z3_L_TRUE
       end
     end))

  fun main (name, args) =
    (display_version();
     simple_example();
     demorgan();
     find_model_example1();
     find_model_example2();
     prove_example1();
     prove_example2();
     push_pop_example1();
     quantifier_example1();
     tutorial_sample();
     OS.Process.success
    )
    handle exn => (print(concat["main:uncaught exception[", exnMessage exn, "]\n"]);
                   OS.Process.failure)
end
val _ =  Main.main (CommandLine.name(), CommandLine.arguments())

