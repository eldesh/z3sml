
structure Main =
struct
  structure Ptr = Pointer
  structure D = Z3.Deprecated

  val LOG_Z3_CALLS = ref false

  fun LOG_MSG msg =
    if !LOG_Z3_CALLS
    then Z3.Z3_append_log msg
    else ()

  fun println s = print(s^"\n")

  fun using get release during =
    let
      val resource = get ()
      val result = during resource handle exn => (release resource; raise exn)
    in
      release resource;
      result
    end

  fun for i cond next f =
    if cond i
    then (f i; for (next i) cond next f)
    else ()

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
        case result
          of Z3.Z3_lbool.Z3_L_FALSE => print "unsat\n"
           | Z3.Z3_lbool.Z3_L_UNDEF =>
               (print "unknown\n";
                print (concat["potential model:\n"
                             , Z3.Z3_model_to_string (ctx, !m)
                             , "\n"]))
           | Z3.Z3_lbool.Z3_L_TRUE  =>
               (print (concat["sat\n"
                             , Z3.Z3_model_to_string (ctx, !m)
                             , "\n"]))
    in
      if not (Ptr.isNull (!m))  then D.Z3_del_model (ctx, !m) else ();
      if result <> expected then raise Fail "unexpected result" else ()
    end

  fun with_config f =
    using Z3.Z3_mk_config
          Z3.Z3_del_config
          f

  fun mk_context () =
    with_config (fn cfg =>
      let
        val () = Z3.Z3_set_param_value (cfg, "model", "true")
        val ctx = Z3.Z3_mk_context cfg
      in
        Z3.Z3_set_error_handler(ctx, SOME (fn _ => print "error\n"));
        ctx
      end)

  fun mk_context_custom cfg error_handler =
    let
      val ()  = Z3.Z3_set_param_value (cfg, "model", "true")
      val ctx = Z3.Z3_mk_context cfg
      val ()  = Z3.Z3_set_error_handler(ctx, error_handler)
    in
      ctx
    end

  fun with_context f =
    using mk_context
          Z3.Z3_del_context
          f

  exception ErrorCode of Z3.Z3_error_code.t

  fun with_ctx_error_handler h f =
    using (fn()=> let val ctx = mk_context () in
                    Z3.Z3_set_error_handler(ctx, h);
                    ctx
                  end)
          Z3.Z3_del_context
          f

  fun mk_proof_context () =
    with_config (fn cfg =>
    let
      val () = Z3.Z3_set_param_value(cfg, "proof", "true")
    in
      mk_context_custom cfg (SOME(fn(_, err)=> raise ErrorCode err))
    end)

  fun lbool_to_string Z3.Z3_lbool.Z3_L_FALSE = "L_FALSE"
    | lbool_to_string Z3.Z3_lbool.Z3_L_UNDEF = "L_UNDEF"
    | lbool_to_string Z3.Z3_lbool.Z3_L_TRUE  = "L_TRUE"
    | lbool_to_string _                  = raise Fail "lbool_to_string"

  fun simple_example () =
    with_context (fn ctx =>
    let val x = D.Z3_check ctx in
      print (concat["CONTEXT:\n"
                   , D.Z3_context_to_string ctx
                   , "END OF CONTEXT\n"])
    end)

  fun demorgan () =
    with_context (fn ctx =>
    let
      val bool_sort = Z3.Z3_mk_bool_sort ctx
      val symbol_x  = Z3.Z3_mk_int_symbol (ctx, 0)
      val symbol_y  = Z3.Z3_mk_int_symbol (ctx, 1)
      val x         = Z3.Z3_mk_const (ctx, symbol_x, bool_sort)
      val y         = Z3.Z3_mk_const (ctx, symbol_y, bool_sort)
      val not_x     = Z3.Z3_mk_not (ctx, x)
      val not_y     = Z3.Z3_mk_not (ctx, y)
      (*
       * De Morgan - with a negation around
       * !(!(x && y) <-> (!x || !y))
       *)
      val args    = Array.fromList [x, y]
      val x_and_y = Z3.Z3_mk_and (ctx, Array.vector args)
      val ls      = Z3.Z3_mk_not (ctx, x_and_y)
      val () = Array.update (args, 0, not_x)
      val () = Array.update (args, 1, not_y)
      val rs                 = Z3.Z3_mk_or (ctx, Array.vector args)
      val conjecture         = Z3.Z3_mk_iff(ctx, ls, rs)
      val negated_conjecture = Z3.Z3_mk_not(ctx, conjecture)
      val () = D.Z3_assert_cnstr (ctx, negated_conjecture)
    in
      case D.Z3_check ctx
        of Z3.Z3_lbool.Z3_L_FALSE => print "DeMorgan is valid\n"
         | Z3.Z3_lbool.Z3_L_TRUE  => print "Undef\n"
         | Z3.Z3_lbool.Z3_L_UNDEF => print "DeMorgan is not valid\n"
    end)

  fun find_model_example1 () =
    with_context (fn ctx =>
    let
      val x = bool_var ctx "x"
      val y = bool_var ctx "y"
      val x_xor_y = Z3.Z3_mk_xor (ctx, x, y)
      val () = D.Z3_assert_cnstr (ctx, x_xor_y)
    in
      print "model for: x xor y\n";
      check ctx Z3.Z3_lbool.Z3_L_TRUE
    end)

  fun find_model_example2 () =
    let
      val cfg = Z3.Z3_mk_config ()
      val ctx = Z3.Z3_mk_context cfg

      val x = int_var ctx "x"
      val y = int_var ctx "y"
      val one = int ctx 1
      val two = int ctx 2

      val y_plus_one = Z3.Z3_mk_add (ctx, Vector.fromList [y, one])

      val c1 = Z3.Z3_mk_lt (ctx, x, y_plus_one)
      val c2 = Z3.Z3_mk_gt (ctx, x, two)

      val () = D.Z3_assert_cnstr (ctx, c1)
      val () = D.Z3_assert_cnstr (ctx, c2)

      val () = print "model for: x < y + 1, x > 2\n"
      val () = check ctx Z3.Z3_lbool.Z3_L_TRUE

      val x_eq_y = Z3.Z3_mk_eq (ctx, x, y)
      val c3     = Z3.Z3_mk_not(ctx, x_eq_y)
    in
      D.Z3_assert_cnstr (ctx, c3);
      print "model for: x < y + 1, x > 2, not(x = y)\n";
      check ctx Z3.Z3_lbool.Z3_L_TRUE;
      Z3.Z3_del_context ctx
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
      val solver = Z3.Z3_mk_solver ctx
      val x = int_var ctx "x"
      val y = int_var ctx "y"
      val two   = int ctx 2
      val seven = int ctx 7
      val ten   = int ctx 10
      fun add ctx (l,r) = Z3.Z3_mk_add (ctx, Vector.fromList [l, r])
      fun mul ctx (l,r) = Z3.Z3_mk_mul (ctx, Vector.fromList [l, r])
      val () = app (fn assert => Z3.Z3_solver_assert (ctx, solver, assert))
                    [ Z3.Z3_mk_gt (ctx, x, two) (* x < 2 *)
                    , Z3.Z3_mk_lt (ctx, y, ten) (* y < 10 *)
                    , Z3.Z3_mk_eq (ctx, add ctx (x, mul ctx (two, y))
                                   , seven) (* x + 2*y = 7 *)
                    ]
      val () = print (Z3.Z3_solver_to_string (ctx, solver) ^ "\n")
      val model =
        case Z3.Z3_solver_check (ctx, solver)
          of Z3.Z3_lbool.Z3_L_TRUE => Z3.Z3_solver_get_model (ctx, solver)
           | _                 => raise Fail "solver_check"
      val decls = Vector.tabulate(
                      Word.toInt (Z3.Z3_model_get_num_consts(ctx, model))
                    , fn i=> Z3.Z3_model_get_const_decl(ctx, model, Word.fromInt i))
    in
      (*
      print (Z3.Z3_model_to_string (ctx, model)^"\n");
      *)
      Vector.app
         (fn decl =>
          let
            val ast = Z3.Z3_model_get_const_interp (ctx, model, decl)
          in
            print (concat[Z3.Z3_func_decl_to_string (ctx, decl)
                         , " -> "
                         ,Z3.Z3_ast_to_string (ctx, ast)
                         , "\n"])
          end)
         decls
    end)

  fun mk_unary_app ctx f x =
    Z3.Z3_mk_app (ctx, f, Vector.fromList [x])

  fun mk_binary_app ctx f x y =
    Z3.Z3_mk_app (ctx, f, Vector.fromList[x,y])

  fun local_ctx ctx f =
    using (fn () => (D.Z3_push ctx; ctx))
          (fn ctx' => D.Z3_pop (ctx', 0w1))
          f

  exception Unexpected of string
  exception Unreachable of string

  fun unreachable locate : unit =
    raise Unreachable (concat["@", locate
                             , " unreachable code was reached"])

  fun prove ctx f is_valid =
    local_ctx ctx (fn ctx =>
    let
      val not_f = Z3.Z3_mk_not (ctx, f)
      val () = D.Z3_assert_cnstr (ctx, not_f)
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val ret = D.Z3_check_and_get_model (ctx, m)
    in
      using (fn()=> m) (fn m=> if not (Ptr.isNull (!m))
                               then D.Z3_del_model (ctx, !m)
                               else ())
      (fn ref m =>
        case ret
          of Z3.Z3_lbool.Z3_L_FALSE =>
                (print "valid\n";
                 if not is_valid then raise Unexpected "prove/valid" else ())
           | Z3.Z3_lbool.Z3_L_UNDEF =>
                (print "unknown\n";
                 if not (Ptr.isNull m)
                 then print(concat["potential counterexample:\n"
                                  , Z3.Z3_model_to_string (ctx, m), "\n"])
                 else ();
                 if is_valid then raise Unexpected "prove/unknown" else ())
           | Z3.Z3_lbool.Z3_L_TRUE =>
                (print "invalid\n";
                 if not (Ptr.isNull m)
                 then print(concat["counterexample:\n"
                                  , Z3.Z3_model_to_string (ctx, m), "\n"])
                 else ();
                 if is_valid then raise Unexpected "prove/invalid" else ()))
    end)

  fun prove_example1() =
     with_context (fn ctx =>
     let
       (* create uninterpreted type *)
       val U_name   = Z3.Z3_mk_string_symbol (ctx, "U")
       val U        = Z3.Z3_mk_uninterpreted_sort (ctx, U_name)
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
       val ()  = D.Z3_assert_cnstr (ctx, Z3.Z3_mk_eq (ctx, x, y))
       (* prove g(x) = g(y) *)
       val f   = Z3.Z3_mk_eq (ctx, gx, gy)
       val ()  = print "prove: x = y implies g(x) = g(y)\n"
       val ()  = prove ctx f Z3.Z3_TRUE
       (* create g(g(x)) *)
       val ggx = mk_unary_app ctx g gx
       (* disprove g(g(x)) = g(y) *)
       val f   = Z3.Z3_mk_eq (ctx, ggx, gy)
     in
       print "disprove: x = y implies g(g(x)) = g(y)\n";
       prove ctx f Z3.Z3_FALSE
     end)

  fun mk_var ctx name ty =
    Z3.Z3_mk_const (ctx, Z3.Z3_mk_string_symbol (ctx, name), ty)

  fun mk_int_var ctx name =
    mk_var ctx name (Z3.Z3_mk_int_sort ctx)

  fun mk_bool_var ctx name =
    mk_var ctx name (Z3.Z3_mk_bool_sort ctx)

  fun mk_int ctx n =
    Z3.Z3_mk_int (ctx, n, Z3.Z3_mk_int_sort ctx)

  fun prove_example2() =
     with_context (fn ctx =>
     let
       (* declare function g *)
       val int_sort = Z3.Z3_mk_int_sort ctx
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
       val gx_gy    = Z3.Z3_mk_sub (ctx, args)
       val ggx_gy   = mk_unary_app ctx g gx_gy
       val eq       = Z3.Z3_mk_eq  (ctx, ggx_gy, gz)
       val c1       = Z3.Z3_mk_not (ctx, eq)
       val () = D.Z3_assert_cnstr (ctx, c1)
       (* assert x + z <= y *)
       val args     = Vector.fromList [x,z]
       val x_plus_z = Z3.Z3_mk_add (ctx, args)
       val c2       = Z3.Z3_mk_le (ctx, x_plus_z, y)
       val () = D.Z3_assert_cnstr (ctx, c2)
       (* assert y <= x *)
       val c3       = Z3.Z3_mk_le (ctx, y, x)
       val () = D.Z3_assert_cnstr (ctx, c3)
     in
       (* prove z < 0 *)
       let
         val f = Z3.Z3_mk_lt (ctx, z, zero)
       in
         print "prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n";
         prove ctx f Z3.Z3_TRUE
       end;
       (* disprove z < ~1 *)
       let
         val minus_one = mk_int ctx ~1
         val f = Z3.Z3_mk_lt (ctx, z, minus_one)
       in
         print "disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n";
         prove ctx f Z3.Z3_FALSE
       end
     end)

  structure Display =
  struct
    fun symbol c out s =
      case Z3.Z3_get_symbol_kind (c, s)
        of Z3.Z3_symbol_kind.Z3_INT_SYMBOL =>
            TextIO.output (out, concat["#", Int.toString
                                           (Z3.Z3_get_symbol_int(c, s))])
         | Z3.Z3_symbol_kind.Z3_STRING_SYMBOL =>
            TextIO.output (out, Z3.Z3_get_symbol_string(c, s))

    fun sort c out ty =
      let
        fun succ w = w + 0w1
        val printf = TextIO.output
      in
        case Z3.Z3_get_sort_kind (c, ty)
          of Z3.Z3_sort_kind.Z3_UNINTERPRETED_SORT =>
                symbol c out (Z3.Z3_get_sort_name (c, ty))
           | Z3.Z3_sort_kind.Z3_BOOL_SORT => printf (out, "bool")
           | Z3.Z3_sort_kind.Z3_INT_SORT  => printf (out, "int")
           | Z3.Z3_sort_kind.Z3_REAL_SORT => printf (out, "real")
           | Z3.Z3_sort_kind.Z3_BV_SORT   =>
               printf (out, concat["bv"
                          , Word.toString(Z3.Z3_get_bv_sort_size(c,ty))])
           | Z3.Z3_sort_kind.Z3_ARRAY_SORT =>
              (printf (out, "[");
               sort c out (Z3.Z3_get_array_sort_domain(c, ty));
               printf (out, "->");
               sort c out (Z3.Z3_get_array_sort_range (c, ty));
               printf (out, "]"))
           | Z3.Z3_sort_kind.Z3_DATATYPE_SORT =>
              ((if Z3.Z3_get_datatype_sort_num_constructors(c, ty) <> 0w1
                then printf (out, Z3.Z3_sort_to_string(c, ty))
                else ());
               printf (out, "(");
               for 0w0 (fn i=> i < Z3.Z3_get_tuple_sort_num_fields(c, ty)) succ
               (fn i=>
                 let
                   val field = Z3.Z3_get_tuple_sort_field_decl(c, ty, i)
                 in
                   (if i > 0w0 then printf (out, ", ") else ());
                   sort c out (Z3.Z3_get_range(c, field))
                 end);
               printf (out, ")"))
           | _ =>
              (printf (out, "unknown[");
               symbol c out (Z3.Z3_get_sort_name(c, ty));
               printf (out, "]"))
      end

    fun ast c out v =
      let
        fun succ w = w + 0w1
      in
        case Z3.Z3_get_ast_kind (c, v)
          of Z3.Z3_ast_kind.Z3_NUMERAL_AST =>
               (TextIO.output (out, Z3.Z3_get_numeral_string (c, v));
                TextIO.output (out, ":");
                sort c out (Z3.Z3_get_sort (c, v)))
           | Z3.Z3_ast_kind.Z3_APP_AST =>
               let
                 val app = Z3.Z3_to_app (c, v)
                 val num_fields = Z3.Z3_get_app_num_args (c, app)
                 val d = Z3.Z3_get_app_decl (c, app)
               in
                 TextIO.output (out, Z3.Z3_func_decl_to_string(c, d));
                 if num_fields > 0w0
                 then
                   (TextIO.output (out, "[");
                    for 0w0 (fn i=> i < num_fields) succ (fn i=>
                      (if i > 0w0 then TextIO.output (out, ", ") else ();
                       ast c out (Z3.Z3_get_app_arg (c, app, i))
                      )
                    );
                    TextIO.output (out, "]")
                   )
                 else
                   ()
               end
           | Z3.Z3_ast_kind.Z3_QUANTIFIER_AST =>
               TextIO.output (out, "quantifier")
           | _ =>
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
          val () = symbol c out (Z3.Z3_get_decl_name(c, fdecl))
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
          TextIO.output(out, ")}\n")
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
          val name = Z3.Z3_get_decl_name (ctx, cnst)
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
      case result
        of Z3.Z3_lbool.Z3_L_FALSE => print "unsat\n"
         | Z3.Z3_lbool.Z3_L_UNDEF =>
            (print "unknown\n";
             print "potential model:\n";
             Display.model ctx TextIO.stdOut (!m))
         | Z3.Z3_lbool.Z3_L_TRUE =>
            (print "sat\n";
             Display.model ctx TextIO.stdOut (!m));
      if not (Ptr.isNull (!m))
      then D.Z3_del_model (ctx, !m) else ();
      if result <> expected_result
      then raise Unexpected "check2"
      else ()
    end

  fun assert_inj_axiom ctx f i =
    let
      val sz = Z3.Z3_get_domain_size (ctx, f)
      val _  = if i >= sz then raise Fail "failed to create inj axiom"
               else ()
      val finv_domain = Z3.Z3_get_range (ctx, f)
      val finv_range  = Z3.Z3_get_domain(ctx, f, i)
      val finv        = Z3.Z3_mk_fresh_func_decl(ctx, "inv"
                            , Vector.fromList[finv_domain], finv_range)
      (* allocate temporary arrays *)
      val types = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Z3_get_domain (ctx, f, Word.fromInt j))
      val names = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Z3_mk_int_symbol (ctx, j))
      val xs    = Vector.tabulate(Word.toInt sz, fn j=>
                     Z3.Z3_mk_bound(ctx, Word.fromInt j, Vector.sub(types, j)))
      val x_i   = Vector.sub (xs, Word.toInt i)
      val fxs   = Z3.Z3_mk_app (ctx, f, xs)
      val finv_fxs = mk_unary_app ctx finv fxs
      val eq       = Z3.Z3_mk_eq (ctx, finv_fxs, x_i)
      val p        = Z3.Z3_mk_pattern(ctx, Vector.fromList[fxs])
      val () = print(concat["pattern: ", Z3.Z3_pattern_to_string(ctx, p), "\n\n"])
      val q  = Z3.Z3_mk_forall (ctx, 0w0, Vector.fromList[p], types, names, eq)
    in
      print(concat["assert axiom:\n", Z3.Z3_ast_to_string(ctx, q), "\n"]);
      D.Z3_assert_cnstr(ctx, q)
    end

  fun search_failure_string sf =
    let
      open Z3.Z3_search_failure
      val db =
        [ (Z3_NO_FAILURE      , "Z3_NO_FAILURE"      )
        , (Z3_UNKNOWN         , "Z3_UNKNOWN"         )
        , (Z3_TIMEOUT         , "Z3_TIMEOUT"         )
        , (Z3_MEMOUT_WATERMARK, "Z3_MEMOUT_WATERMARK")
        , (Z3_CANCELED        , "Z3_CANCELED"        )
        , (Z3_NUM_CONFLICTS   , "Z3_NUM_CONFLICTS"   )
        , (Z3_THEORY          , "Z3_THEORY"          )
        , (Z3_QUANTIFIERS     , "Z3_QUANTIFIERS"     )
        ]
    in
      case List.find (fn (e,_)=> sf=e) db
        of SOME (_,s) => s
         | NONE => raise Fail "search_failure_string"
    end

  fun quantifier_example1() =
    let
      val ctx = with_config (fn cfg =>
                 (Z3.Z3_global_param_set("smt.mbqi.max_iterations", "10");
                  mk_context_custom cfg (SOME(fn _ => print "error\n"))
                 ))
      (* declare function f *)
      val int_sort = Z3.Z3_mk_int_sort ctx
      val f_name   = Z3.Z3_mk_string_symbol (ctx, "f")
      val f_domain = Vector.fromList [int_sort, int_sort]
      val f        = Z3.Z3_mk_func_decl(ctx, f_name, f_domain, int_sort)
    in
      (* assert that f is injective in the second argument. *)
      assert_inj_axiom ctx f 0w1;
    let
      (* create x, y, v, w, fxy, fwv *)
      val x = mk_int_var ctx "x"
      val y = mk_int_var ctx "y"
      val v = mk_int_var ctx "v"
      val w = mk_int_var ctx "w"
      val fxy = mk_binary_app ctx f x y
      val fwv = mk_binary_app ctx f w v

      (* assert f(x, y) = f(w, v) *)
      val p1 = Z3.Z3_mk_eq (ctx, fxy, fwv)
    in
      D.Z3_assert_cnstr(ctx, p1);
    let
      (* prove f(x, y) = f(w, v) implies y = v *)
      val p2 = Z3.Z3_mk_eq (ctx, y, v)
    in
      print "prove: f(x, y) = f(w, v) implies y = v\n";
      prove ctx p2 Z3.Z3_TRUE;
    let
      (* disprove f(x, y) = f(w, v) implies x = w *)
      (* using check2 instead of prove *)
      val p3     = Z3.Z3_mk_eq (ctx, x, w)
      val not_p3 = Z3.Z3_mk_not(ctx, p3)
    in
      D.Z3_assert_cnstr(ctx, not_p3);
      print "disprove: f(x, y) = f(w, v) implies x = w\n";
      print "that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n";
      check2 ctx Z3.Z3_lbool.Z3_L_UNDEF;
      print(concat["reason for last failure: "
                  , search_failure_string (D.Z3_get_search_failure ctx)
                  , " (7 = quantifiers)\n"]);
      if D.Z3_get_search_failure ctx <> Z3.Z3_search_failure.Z3_QUANTIFIERS
      then raise Fail "unexpected result" else ()
    end end end;
      Z3.Z3_del_context ctx;
      Z3.Z3_global_param_reset_all()
    end

  fun push_pop_example1 () =
    with_context (fn ctx =>
    let
      (* create a big number *)
      val int_sort   = Z3.Z3_mk_int_sort ctx
      val big_number = Z3.Z3_mk_numeral
                        (ctx, "1000000000000000000000000000000000000000000000000000000", int_sort)
      (* create number 3 *)
      val three      = Z3.Z3_mk_numeral (ctx, "3", int_sort)
      (* create x *)
      val x_sym      = Z3.Z3_mk_string_symbol (ctx, "x")
      val x          = Z3.Z3_mk_const (ctx, x_sym, int_sort)
      (* assert x >= "big number" *)
      val c1         = Z3.Z3_mk_ge (ctx, x, big_number)
      val ()         = print "assert: x >= 'big number'\n"
      val ()         = D.Z3_assert_cnstr(ctx, c1)
      (* create a backtracking point *)
      val ()         = print "push\n"
    in
      local_ctx ctx (fn ctx =>
      let
        val () = print (concat["number of scopes: "
                              , Word.toString (D.Z3_get_num_scopes ctx)
                              , "\n"])
        val c2 = Z3.Z3_mk_le (ctx, x, three)
        val () = print "assert: x <= 3\n"
        val () = D.Z3_assert_cnstr (ctx, c2)
      in
        (* context is inconsistent at this point *)
        check2 ctx Z3.Z3_lbool.Z3_L_FALSE;
        (* backtrack: the constraint x <= 3 will be removed, since it was
         * asserted after the last Z3_push. *)
        print "pop\n"
      end);
      print (concat["number of scopes: "
           , Word.toString (D.Z3_get_num_scopes ctx), "\n"]);
      (* the context is consistent again. *)
      check2 ctx Z3.Z3_lbool.Z3_L_TRUE;

      (* new constraints can be asserted... *)
      let
        (* create y *)
        val y_sym = Z3.Z3_mk_string_symbol (ctx, "y")
        val y     = Z3.Z3_mk_const (ctx, y_sym, int_sort)
        (* assert y > x *)
        val c3    = Z3.Z3_mk_gt(ctx, y, x)
      in
        print "assert: y > x\n";
        D.Z3_assert_cnstr(ctx, c3);
        (* the context is still consistent *)
        check2 ctx Z3.Z3_lbool.Z3_L_TRUE
      end
    end)

  fun array_example1 () =
    with_context (fn ctx =>
    let
      val int_sort   = Z3.Z3_mk_int_sort ctx
      val array_sort = Z3.Z3_mk_array_sort (ctx, int_sort, int_sort)

      val a1   = mk_var ctx "a1" array_sort
      val a2   = mk_var ctx "a2" array_sort
      val i1   = mk_var ctx "i1" int_sort
      val i2   = mk_var ctx "i2" int_sort
      val i3   = mk_var ctx "i3" int_sort
      val v1   = mk_var ctx "v1" int_sort
      val v2   = mk_var ctx "v2" int_sort

      val st1  = Z3.Z3_mk_store (ctx, a1, i1, v1)
      val st2  = Z3.Z3_mk_store (ctx, a2, i2, v2)

      val sel1 = Z3.Z3_mk_select (ctx, a1, i3)
      val sel2 = Z3.Z3_mk_select (ctx, a2, i3)

      (* create antecedent *)
      val antecedent = Z3.Z3_mk_eq (ctx, st1, st2)

      (* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) *)
      val consequent = Z3.Z3_mk_or (ctx, Vector.fromList [
                                        Z3.Z3_mk_eq (ctx, i1, i3),
                                        Z3.Z3_mk_eq (ctx, i2, i3),
                                        Z3.Z3_mk_eq (ctx, sel1, sel2)
                                      ])

      (* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) *)
      val thm = Z3.Z3_mk_implies (ctx, antecedent, consequent)
    in
      print "prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))\n";
      print(concat[Z3.Z3_ast_to_string (ctx, thm), "\n"]);
      prove ctx thm Z3.Z3_TRUE
    end)

  fun array_example2 () =
    with_context (fn ctx =>
    let
      fun succ n = n + 0w1
    in
      for 0w2 (fn n=> n<=0w5) succ (fn n=>
      with_context (fn ctx =>
      let
        val () = print(concat["n = ", Word.toString n, "\n"])
        val bool_sort = Z3.Z3_mk_bool_sort ctx
        val array_sort = Z3.Z3_mk_array_sort (ctx, bool_sort, bool_sort)
        val a = Vector.tabulate(Word.toInt n, fn i=>
                   Z3.Z3_mk_const (ctx, Z3.Z3_mk_int_symbol (ctx, i), array_sort))
        (* assert distinct(a[0], ..., a[n]) *)
        val d = Z3.Z3_mk_distinct(ctx, a)
      in
        println (Z3.Z3_ast_to_string(ctx, d));
        D.Z3_assert_cnstr (ctx, d);
        (* context is satisfiable if n < 5 *)
        check2 ctx (if n < 0w5
                    then Z3.Z3_lbool.Z3_L_TRUE
                    else Z3.Z3_lbool.Z3_L_FALSE)
      end))
    end)

  fun array_example3 () =
    with_context (fn ctx =>
    let
      val bool_sort  = Z3.Z3_mk_bool_sort ctx
      val int_sort   = Z3.Z3_mk_int_sort ctx
      val array_sort = Z3.Z3_mk_array_sort (ctx, int_sort, bool_sort)
      val () = if Z3.Z3_get_sort_kind (ctx, array_sort)
                   <> Z3.Z3_sort_kind.Z3_ARRAY_SORT
               then raise Fail "type must be an array type"
               else ()
      (* 'domain -> 'range *)
      val domain = Z3.Z3_get_array_sort_domain (ctx, array_sort)
      val range  = Z3.Z3_get_array_sort_range  (ctx, array_sort)
    in
      print "domain: ";
      Display.sort ctx TextIO.stdOut domain;
      print "\n";
      print "range:  ";
      Display.sort ctx TextIO.stdOut range;
      print "\n";
      if int_sort <> domain orelse bool_sort <> range
      then raise Fail "invalid array type" else ()
    end)

  fun mk_real_var ctx name =
    mk_var ctx name (Z3.Z3_mk_real_sort ctx)

  exception TypeMismatch of {exp:Z3.Z3_sort_kind.t, act:Z3.Z3_sort_kind.t}

  fun check_type (exp:Z3.Z3_sort_kind.t) act =
    if exp <> act
    then raise TypeMismatch {exp=exp, act=act}
    else ()

  fun mk_tuple_update c t i new_val =
    let
      val ty = Z3.Z3_get_sort (c, t)
      val () = check_type Z3.Z3_sort_kind.Z3_DATATYPE_SORT (Z3.Z3_get_sort_kind (c, ty))
      val num_fields = Z3.Z3_get_tuple_sort_num_fields (c, ty)
      val () = if i >= num_fields
               then raise Fail "invalid tuple update, index is too big"
               else ()
      val new_fields = Vector.tabulate (Word.toInt num_fields, fn j=>
            if i = Word.fromInt j
            then
              new_val (* use new_val at positio i *)
            else
              (* use field j of t *)
              let val proj_decl = Z3.Z3_get_tuple_sort_field_decl (c, ty, Word.fromInt j)
              in
                mk_unary_app c proj_decl t
              end)
      val mk_tuple_decl = Z3.Z3_get_tuple_sort_mk_decl (c, ty)
    in
      Z3.Z3_mk_app (c, mk_tuple_decl, new_fields)
    end

  fun tuple_example1 () =
    with_context (fn ctx =>
    let
      val real_sort = Z3.Z3_mk_real_sort ctx
      (* create pair (tuple) type *)
      val mk_tuple_name = Z3.Z3_mk_string_symbol (ctx, "mk_pair")
      val proj_names = Vector.fromList [
                         Z3.Z3_mk_string_symbol (ctx, "get_x"),
                         Z3.Z3_mk_string_symbol (ctx, "get_y")
                       ]
      val proj_sorts = Vector.fromList [ real_sort, real_sort ]
      (* Z3_mk_tule_sort will set mk_tuple_decl and proj_decls *)
      val mk_tuple_decl : Z3.Z3_func_decl ref = ref (Ptr.NULL())
      val proj_decls : Z3.Z3_func_decl array = Array.fromList [Ptr.NULL(), Ptr.NULL()]
      val pair_sort = Z3.Z3_mk_tuple_sort (ctx, mk_tuple_name, proj_names
                                                , proj_sorts, mk_tuple_decl, proj_decls)
      (* function that extracts the first element of a tuple. *)
      val get_x_decl = Array.sub (proj_decls, 0)
      (* function that extracts the second element of a tuple. *)
      val get_y_decl = Array.sub (proj_decls, 1)
      val () = print "tuple_sort: "
      val () = Display.sort ctx TextIO.stdOut pair_sort
      val () = print "\n"
    in
      (* prove that get_x(mk_pair(x,y)) == 1 implies x = 1 *)
      let
        val x    = mk_real_var ctx "x"
        val y    = mk_real_var ctx "y"
        val app1 = mk_binary_app ctx (!mk_tuple_decl) x y
        val app2 = mk_unary_app ctx get_x_decl app1
        val one  = Z3.Z3_mk_numeral (ctx, "1", real_sort)
        val eq1  = Z3.Z3_mk_eq (ctx, app2, one)
        val eq2  = Z3.Z3_mk_eq (ctx,    x, one)
        val thm  = Z3.Z3_mk_implies(ctx, eq1, eq2)
        val () = print "prove: get_x(mk_pair(x, y)) = 1 implies x = 1\n"
        val () = prove ctx thm Z3.Z3_TRUE
        (* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1 *)
        val eq3 = Z3.Z3_mk_eq (ctx, y, one)
        val thm = Z3.Z3_mk_implies (ctx, eq1, eq3)
        val () = print "disprove: get_x(mk_pair(x, y)) = 1 implies y = 1\n"
        val () = prove ctx thm Z3.Z3_FALSE
      in () end;
      let
        (* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 *)
        val p1 = mk_var ctx "p1" pair_sort
        val p2 = mk_var ctx "p2" pair_sort
        val x1 = mk_unary_app ctx get_x_decl p1
        val y1 = mk_unary_app ctx get_y_decl p1
        val x2 = mk_unary_app ctx get_x_decl p2
        val y2 = mk_unary_app ctx get_y_decl p2
        val antecedents = Vector.fromList [
                            Z3.Z3_mk_eq (ctx, x1, x2),
                            Z3.Z3_mk_eq (ctx, y1, y2)
                          ]
        val antecedent = Z3.Z3_mk_and (ctx, antecedents)
        val consequent = Z3.Z3_mk_eq (ctx, p1, p2)
        val thm = Z3.Z3_mk_implies (ctx, antecedent, consequent)
        val () = print "prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2\n"
        val () = prove ctx thm Z3.Z3_TRUE
        (* disprove that get_x(p1) = get_x(p2) implies p1 = p2 *)
        val thm = Z3.Z3_mk_implies (ctx, Vector.sub(antecedents,0), consequent)
        val () = print "disprove: get_x(p1) = get_x(p2) implies p1 = p2\n"
        val () = prove ctx thm Z3.Z3_FALSE
      in () end;
      (* demonstrate how to use the mk_tuple_update function *)
      (* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 *)
      let
        val p1 = mk_var ctx "p1" pair_sort
        val p2 = mk_var ctx "p2" pair_sort
        val one = Z3.Z3_mk_numeral (ctx, "1" , real_sort)
        val ten = Z3.Z3_mk_numeral (ctx, "10", real_sort)
        val updt = mk_tuple_update ctx p1 0w0 ten
        val antecedent = Z3.Z3_mk_eq (ctx, p2, updt)
        val x = mk_unary_app ctx get_x_decl p2
        val consequent = Z3.Z3_mk_eq (ctx, x, ten)
        val thm = Z3.Z3_mk_implies (ctx, antecedent, consequent)
        val () = print "prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10\n"
        val () = prove ctx thm Z3.Z3_TRUE
        (* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 *)
        val y = mk_unary_app ctx get_y_decl p2
        val consequent = Z3.Z3_mk_eq (ctx, y, ten)
        val thm = Z3.Z3_mk_implies (ctx, antecedent, consequent)
      in
        print "disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10\n";
        prove ctx thm Z3.Z3_FALSE
      end
    end)

  fun bitvector_example1 () =
    with_context (fn ctx =>
    let
      val bv_sort = Z3.Z3_mk_bv_sort (ctx, 0w32)
      val x    = mk_var ctx "x" bv_sort
      val zero = Z3.Z3_mk_numeral (ctx,  "0", bv_sort)
      val ten  = Z3.Z3_mk_numeral (ctx, "10", bv_sort)
      val x_minus_ten = Z3.Z3_mk_bvsub (ctx, x, ten)
      (* bvsle is signed less than or equal to *)
      val c1 = Z3.Z3_mk_bvsle(ctx, x, ten)
      val c2 = Z3.Z3_mk_bvsle(ctx, x_minus_ten, zero)
      val thm = Z3.Z3_mk_iff (ctx, c1, c2)
    in
      print "disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers\n";
      prove ctx thm Z3.Z3_FALSE
    end)

  (* Find x and y such that: x ^ y - 103 == x * y *)
  fun bitvector_example2 () =
    with_context (fn ctx =>
    let
      val () = print "find values of x and y, such that x ^ y - 103 == x * y\n"
      val bv_sort = Z3.Z3_mk_bv_sort (ctx, 0w32)
      val x       = mk_var ctx "x" bv_sort
      val y       = mk_var ctx "y" bv_sort
      val x_xor_y = Z3.Z3_mk_bvxor(ctx, x, y)
      val c103    = Z3.Z3_mk_numeral(ctx, "103", bv_sort)
      val lhs     = Z3.Z3_mk_bvsub (ctx, x_xor_y, c103)
      val rhs     = Z3.Z3_mk_bvmul (ctx, x, y)
      val ctr     = Z3.Z3_mk_eq (ctx, lhs, rhs)
    in
      (* add the constraint x ^ y - 103 == x * y to the logical context *)
      D.Z3_assert_cnstr(ctx, ctr);
      (* find a model (i.e., values for x an y that satisfy the constraint *)
      check ctx Z3.Z3_lbool.Z3_L_TRUE
    end)

  fun eval_example1 () =
    with_context (fn ctx =>
    let
      val x = mk_int_var ctx "x"
      val y = mk_int_var ctx "y"
      val two = mk_int ctx 2
      (* assert x < y *)
      val c1 = Z3.Z3_mk_lt (ctx, x, y)
      val () = D.Z3_assert_cnstr(ctx, c1)
      (* assert x > 2 *)
      val c2 = Z3.Z3_mk_gt(ctx, x, two)
      val () = D.Z3_assert_cnstr(ctx, c2)
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
    in
      (* find model for the constraints above *)
      if D.Z3_check_and_get_model (ctx, m) = Z3.Z3_lbool.Z3_L_TRUE
      then
        (print(concat["MODEL:\n", Z3.Z3_model_to_string(ctx, !m)]);
         let val x_plus_y = Z3.Z3_mk_add (ctx, Vector.fromList[x,y]) in
         print "\nevaluating x+y\n";
         let val v = ref (Ptr.NULL()) in
         if D.Z3_eval(ctx, !m, x_plus_y, v)
         then
           (print "result = ";
            Display.ast ctx TextIO.stdOut (!v);
            print "\n"
           )
         else
           raise Fail "failed to evaluate: x+y"
         end end)
      else
        raise Fail "the constraints are satisfiable"
    end)

  fun two_contexts_example1 () =
    let
      open Z3
      val ctx1 = mk_context ()
      val ctx2 = mk_context ()
      val x1 = Z3_mk_const (ctx1, Z3_mk_int_symbol(ctx1, 0), Z3_mk_bool_sort ctx1)
      val x2 = Z3_mk_const (ctx2, Z3_mk_int_symbol(ctx2, 0), Z3_mk_bool_sort ctx2)
    in
      Z3_del_context ctx1;
      (* ctx2 can still be used. *)
      print(concat[Z3_ast_to_string(ctx2, x2), "\n"]);
      Z3_del_context ctx2
    end

  fun check_cond cond msg =
    if cond()
    then
      case msg
        of SOME msg => raise Fail msg
         | NONE     => raise Fail "unexpected result"
    else ()

  fun error_code_example1 () =
    let
      open Z3
      val ctx = with_config (fn cfg => mk_context_custom cfg NONE)
      val x      = bool_var ctx "x"
      val x_decl = Z3_get_app_decl(ctx, Z3_to_app(ctx, x))
      val () = D.Z3_assert_cnstr (ctx, x)
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val v : Z3.Z3_ast ref = ref (Ptr.NULL())
    in
      check_cond (fn()=> D.Z3_check_and_get_model(ctx, m) <> Z3.Z3_lbool.Z3_L_TRUE)
                 NONE;
      check_cond (fn()=> D.Z3_eval_func_decl(ctx, !m, x_decl, v) = Z3_FALSE)
                 (SOME "did not obtain value for declaration.\n");
      if Z3_get_error_code ctx = Z3.Z3_error_code.Z3_OK
      then print "last call succeeded.\n" else ();
      let val str = Z3_get_numeral_string(ctx, !v) in
        (* The following call will fail since the value of x is a boolean *)
        if Z3_get_error_code ctx <> Z3.Z3_error_code.Z3_OK
        then print "last call failed.\n" else ()
      end;
      D.Z3_del_model (ctx, !m);
      Z3.Z3_del_context ctx
    end

  fun error_code_example2 () =
    with_ctx_error_handler (SOME(fn(_, err)=> raise ErrorCode err))
    (fn ctx =>
    let
      val x   = int_var ctx "x"
      val y   = int_var ctx "y"
      val ()  = print "before Z3_mk_iff\n"
      (* the next call will produce an error *)
      val app = Z3.Z3_mk_iff(ctx, x, y)
    in
      unreachable "error_code_example2"
    end)
    handle (ErrorCode c) =>
      print(concat["Z3 error: ", D.Z3_get_error_msg c, ".\n"])

  fun parser_example1 () =
    with_context (fn ctx =>
    let
      val () = Z3.Z3_parse_smtlib_string(
                 ctx,
                 "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
                 Vector.fromList[], Vector.fromList[],
                 Vector.fromList[], Vector.fromList[])
      val num_formulas = Z3.Z3_get_smtlib_num_formulas ctx
    in
      for 0w0 (fn i=> i<num_formulas) (fn i=>i+0w1) (fn i=>
        let val f = Z3.Z3_get_smtlib_formula(ctx, i) in
          print(concat["formula "
                      , Word.toString i, ": "
                      , Z3.Z3_ast_to_string(ctx, f)
                      , "\n"]);
          D.Z3_assert_cnstr(ctx, f)
        end);
      check ctx Z3.Z3_lbool.Z3_L_TRUE
    end)

  fun parser_example2 () =
    with_context (fn ctx =>
    let
      val x = int_var ctx "x"
      val y = int_var ctx "y"
      val decls = Vector.fromList[
                    Z3.Z3_get_app_decl(ctx, Z3.Z3_to_app(ctx, x)),
                    Z3.Z3_get_app_decl(ctx, Z3.Z3_to_app(ctx, y))
                  ]
      val names = Vector.fromList[
                    Z3.Z3_mk_string_symbol (ctx, "a"),
                    Z3.Z3_mk_string_symbol (ctx, "b")
                  ]
      val () = Z3.Z3_parse_smtlib_string(
                 ctx,
                 "(benchmark tst :formula (> a b))",
                 Vector.fromList[],
                 Vector.fromList[],
                 names, decls)
      val f  = Z3.Z3_get_smtlib_formula(ctx, 0w0)
    in
      print(concat["formula: "
                  , Z3.Z3_ast_to_string(ctx, f)
                  , "\n"]);
      D.Z3_assert_cnstr(ctx, f);
      check ctx Z3.Z3_lbool.Z3_L_TRUE
    end)

  fun assert_comm_axiom ctx f =
    let
      val t = Z3.Z3_get_range (ctx, f)
    in
      check_cond (fn()=>
                    Z3.Z3_get_domain_size(ctx, f) <> 0w2 orelse
                    Z3.Z3_get_domain(ctx, f, 0w0) <> t orelse
                    Z3.Z3_get_domain(ctx, f, 0w1) <> t)
        (SOME "function must be binary, and argument types must be equal to return type");
      let
        (* Inside the parser, function f will be referenced using the symbol 'f'. *)
        val f_name = Z3.Z3_mk_string_symbol(ctx, "f")
        (* Inside the parser, type t will be referenced using the symbol 'T'. *)
        val t_name = Z3.Z3_mk_string_symbol(ctx, "T")
        fun ` x = Vector.fromList [x]
      in
        Z3.Z3_parse_smtlib_string(
                    ctx,
                    "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))",
                    `t_name, `t,
                    `f_name, `f);
      let
        val q = Z3.Z3_get_smtlib_formula(ctx, 0w0)
      in
        print(concat["assert axiom:\n"
                    , Z3.Z3_ast_to_string(ctx, q), "\n"]);
        D.Z3_assert_cnstr(ctx, q)
      end end
    end

  fun parser_example3 () =
    with_context (fn ctx =>
    let
      val int_sort = Z3.Z3_mk_int_sort ctx
      val g_name   = Z3.Z3_mk_string_symbol(ctx, "g")
      val g_domain = Vector.fromList[int_sort, int_sort]
      val g        = Z3.Z3_mk_func_decl(
                       ctx,
                       g_name,
                       g_domain,
                       int_sort)
      val ` = Vector.fromList
    in
      assert_comm_axiom ctx g;
      (* forall x y, x=y => (g x 0) = (g 0 y) *)
      Z3.Z3_parse_smtlib_string(
        ctx,
        "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))",
        `[], `[],
        `[g_name], `[g]);
      let val thm = Z3.Z3_get_smtlib_formula(ctx, 0w0) in
        print(concat["formula: ",
                     Z3.Z3_ast_to_string(ctx, thm), "\n"]);
        prove ctx thm Z3.Z3_TRUE
      end
    end)

  fun parser_example4 () =
    with_context (fn ctx =>
    let
      val vec = Vector.fromList
      val () = Z3.Z3_parse_smtlib_string(
                 ctx,
                 "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
                 vec[], vec[],
                 vec[], vec[])
      fun for' n = for 0w0 (fn i=> i<n) (fn i=>i+0w1)
    in
      for' (Z3.Z3_get_smtlib_num_decls ctx) (fn i=>
        let val d = Z3.Z3_get_smtlib_decl(ctx, i) in
          print(concat["declaration "
                      , Word.toString i
                      , ": "
                      , Z3.Z3_func_decl_to_string(ctx, d), "\n"])
        end);

      for' (Z3.Z3_get_smtlib_num_assumptions ctx) (fn i=>
        let val a = Z3.Z3_get_smtlib_assumption(ctx, i) in
          print(concat["assumption "
                      , Word.toString i
                      , ": "
                      , Z3.Z3_ast_to_string(ctx, a), "\n"])
        end);

      for' (Z3.Z3_get_smtlib_num_formulas ctx) (fn i=>
        let val f = Z3.Z3_get_smtlib_formula(ctx, i) in
          print(concat["formula "
                      , Word.toString i
                      , ": "
                      , Z3.Z3_ast_to_string(ctx, f), "\n"])
        end)
    end)

  fun parser_example5 () =
    with_ctx_error_handler (SOME(fn(_, err)=> raise ErrorCode err))
    (fn ctx=>
    let
      val vec = Vector.fromList
    in
      (* the following string has a parsing error: missing parenthesis *)
      Z3.Z3_parse_smtlib_string(
                 ctx,
                 "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))",
                 vec[], vec[],
                 vec[], vec[]);
      unreachable "parser_example5"
    end handle ErrorCode err =>
                 (print(concat["Z3 error: "
                              , Z3.Z3_get_error_msg_ex(ctx, err), ".\n"
                              ,"Error message: '"
                              , Z3.Z3_get_smtlib_error ctx, "'.\n"])))

  fun numeral_example () =
    with_context (fn ctx =>
    let
      val real_ty = Z3.Z3_mk_real_sort ctx
      val n1 = Z3.Z3_mk_numeral(ctx, "1/2", real_ty)
      val n2 = Z3.Z3_mk_numeral(ctx, "0.5", real_ty)
    in
      print(concat["Numerals n1:", Z3.Z3_ast_to_string(ctx, n1)
                  ," n2:", Z3.Z3_ast_to_string(ctx, n2), "\n"]);
      prove ctx (Z3.Z3_mk_eq(ctx, n1, n2)) Z3.Z3_TRUE;
    let
      val n1 = Z3.Z3_mk_numeral(ctx, "-1/3", real_ty)
      val n2 = Z3.Z3_mk_numeral(ctx, "-0.33333333333333333333333333333333333333333333333333", real_ty)
    in
      print(concat["Numerals n1:", Z3.Z3_ast_to_string(ctx, n1)
                  ," n2:", Z3.Z3_ast_to_string(ctx, n2), "\n"]);
      prove ctx (Z3.Z3_mk_not(ctx, Z3.Z3_mk_eq(ctx, n1, n2))) Z3.Z3_TRUE
    end end)

  fun ite_example () =
    with_context (fn ctx =>
    let
      val f    = Z3.Z3_mk_false ctx
      val one  = mk_int ctx 1
      val zero = mk_int ctx 0
      val ite  = Z3.Z3_mk_ite(ctx, f, one, zero)
    in
      print(concat["term: "
                  , Z3.Z3_ast_to_string(ctx, ite)
                  , "\n"])
    end)

  fun list_example () =
    with_context (fn ctx =>
    let
      val int_ty = Z3.Z3_mk_int_sort ctx
      val nil_decl     = ref (Ptr.NULL())
      val is_nil_decl  = ref (Ptr.NULL())
      val cons_decl    = ref (Ptr.NULL())
      val is_cons_decl = ref (Ptr.NULL())
      val head_decl    = ref (Ptr.NULL())
      val tail_decl    = ref (Ptr.NULL())
      val int_list = Z3.Z3_mk_list_sort(ctx
                                            , Z3.Z3_mk_string_symbol(ctx, "int_list")
                                            , int_ty
                                            , nil_decl
                                            , is_nil_decl
                                            , cons_decl
                                            , is_cons_decl
                                            , head_decl
                                            , tail_decl)
      fun Cons x xs =
        mk_binary_app ctx (!cons_decl) x xs

      val Nil = Z3.Z3_mk_app(ctx, !nil_decl, Vector.fromList[])
      val l1  = Cons (mk_int ctx 1) Nil
      val l2  = Cons (mk_int ctx 2) Nil
      fun == ctx (x,y) = Z3.Z3_mk_eq(ctx, x, y)
      infixr ==>
      fun p ==> q = fn c => Z3.Z3_mk_implies(c, p, q)
    in
      (* nil <> cons(1, nil) *)
      prove ctx (Z3.Z3_mk_not(ctx, == ctx (l1, l2))) Z3.Z3_TRUE;
      (* cons(2,nil) <> cons(1, nil) *)
      prove ctx (Z3.Z3_mk_not(ctx, == ctx (l1, l2))) Z3.Z3_TRUE;
    let
      (* cons(x,nil) = cons(y,nil) => x = y *)
      val x = mk_var ctx "x" int_ty
      val y = mk_var ctx "y" int_ty
      val l1 = Cons x Nil
	  val l2 = Cons y Nil
    in
      prove ctx ((== ctx (l1,l2) ==> == ctx (x,y)) ctx)
                Z3.Z3_TRUE;
    let
      (* cons(x,u) = cons(x,v) => u = v *)
      val u = mk_var ctx "u" int_list
      val v = mk_var ctx "v" int_list
      val l1 = Cons x u
	  val l2 = Cons y v
    in
      prove ctx ((== ctx (l1,l2) ==> == ctx (u, v)) ctx) Z3.Z3_TRUE;
      prove ctx ((== ctx (l1,l2) ==> == ctx (x, y)) ctx) Z3.Z3_TRUE;
    let
      val ors = Vector.fromList[
                  Z3.Z3_mk_app(ctx, !is_nil_decl, Vector.fromList[u]),
                  Z3.Z3_mk_app(ctx, !is_cons_decl, Vector.fromList[u])
                ]
    in
      (* is_nil(u) or is_cons(u) *)
      prove ctx (Z3.Z3_mk_or(ctx, ors)) Z3.Z3_TRUE;
      (* occurs check u <> cons(x,u) *)
      prove ctx (Z3.Z3_mk_not(ctx, == ctx (u, l1))) Z3.Z3_TRUE;
    let
      fun Head xs = mk_unary_app ctx (!head_decl) xs
      fun Tail xs = mk_unary_app ctx (!tail_decl) xs
      (* destructors: is_cons(u) => u = cons(head(u),tail(u)) *)
      val fml1 = == ctx (u, (Cons (Head u) (Tail u)))
      val fml  = (Z3.Z3_mk_app(ctx, !is_cons_decl, Vector.fromList[u])
                  ==> fml1) ctx
    in
      print(concat["Formula ", Z3.Z3_ast_to_string(ctx, fml), "\n"]);
      prove ctx fml Z3.Z3_TRUE;
      prove ctx fml1 Z3.Z3_FALSE
    end end end end end)

  fun tree_example () =
    with_context (fn ctx =>
    let
      infix  ==  !=
      infixr ==>
      fun p ==> q = Z3.Z3_mk_implies(ctx, p, q)
      fun p ==  q = Z3.Z3_mk_eq(ctx, p, q)
      fun p !=  q = Z3.Z3_mk_not(ctx, Z3.Z3_mk_eq(ctx, p, q))

      fun Sym sym = Z3.Z3_mk_string_symbol(ctx, sym)
      fun ptr_ref () = ref (Ptr.NULL())

      val vec = Vector.fromList
      val head_tail = vec[Sym "car", Sym "cdr"]
      fun empty () = vec[]

      (* nil *)
      val nil_con = Z3.Z3_mk_constructor(ctx
                                     , Sym "nil", Sym "is_nil"
                                     , empty(), empty(), empty())
      (* cons of T0 * T0 *)
      val cons_con = Z3.Z3_mk_constructor(ctx
                                     , Sym "cons"
                                     , Sym "is_cons"
                                     , head_tail
                                     , vec[NONE, NONE]
                                     , vec[0w0, 0w0])
      val constructors = Array.fromList[nil_con, cons_con]
      val cell = Z3.Z3_mk_datatype(ctx, Sym "cell", constructors)

      val ( nil_decl,  is_nil_decl) = (ptr_ref(), ptr_ref())
      val (cons_decl, is_cons_decl) = (ptr_ref(), ptr_ref())
      val cons_accessors = Array.fromList[Ptr.NULL(), Ptr.NULL()]
      val () = Z3.Z3_query_constructor(ctx,  nil_con,  nil_decl,  is_nil_decl, Array.fromList[])
      val () = Z3.Z3_query_constructor(ctx, cons_con, cons_decl, is_cons_decl, cons_accessors)
      val car_decl = Array.sub(cons_accessors, 0)
      val cdr_decl = Array.sub(cons_accessors, 1)
      val () = Z3.Z3_del_constructor(ctx, nil_con)
      val () = Z3.Z3_del_constructor(ctx, cons_con)

      fun Cons x xs = mk_binary_app ctx (!cons_decl) x xs
      val Nil = Z3.Z3_mk_app (ctx, !nil_decl, empty())
      fun Car t = mk_unary_app ctx car_decl t
      fun Cdr t = mk_unary_app ctx cdr_decl t
      val l1  = Cons Nil Nil
      val l2  = Cons l1  Nil
    in
      (* nil <> cons(nil, nil) *)
      prove ctx (Nil != l1) Z3.Z3_TRUE;
    let
      val u = mk_var ctx "u" cell
      val v = mk_var ctx "v" cell
      val x = mk_var ctx "x" cell
      val y = mk_var ctx "y" cell
    in
      prove ctx ((Cons x u == Cons y v) ==> (u == v)) Z3.Z3_TRUE;
      prove ctx ((Cons x u == Cons y v) ==> (x == y)) Z3.Z3_TRUE;
    let
      (* is_nil(u) or is_cons(u) *)
      val ors = vec[
                  Z3.Z3_mk_app(ctx,  !is_nil_decl, vec[u]),
                  Z3.Z3_mk_app(ctx, !is_cons_decl, vec[u])
                ]
    in
      prove ctx (Z3.Z3_mk_or(ctx, ors)) Z3.Z3_TRUE;
      (* occurs check u <> cons(x,u) *)
      prove ctx (u != Cons x u) Z3.Z3_TRUE;
    let
      (* desctructors: is_cons(u) => u = cons(car(u),cdr(u)) *)
      val fml1 = u == Cons (Car u) (Cdr u)
      val fml  = Z3.Z3_mk_app(ctx, !is_cons_decl, vec[u])
                 ==> fml1
    in
      print(concat["Formula "
                  , Z3.Z3_ast_to_string(ctx, fml)
                  , "\n"]);
      prove ctx fml Z3.Z3_TRUE;
      prove ctx fml1 Z3.Z3_FALSE
    end end end end)

  (** 
   * Create a forest of trees.
   *
   * forest ::= nil | cons(tree, forest)
   * tree   ::= nil | cons(forest, forest)
   *)
  fun forest_example () =
    with_context (fn ctx =>
    let
      infix == !=
      infixr ==>
      fun p ==> q = Z3.Z3_mk_implies(ctx, p, q)
      fun p ==  q = Z3.Z3_mk_eq(ctx, p, q)
      fun p !=  q = Z3.Z3_mk_not(ctx, Z3.Z3_mk_eq(ctx, p, q))

      val vec = Vector.fromList
      fun empty () = vec[]
      fun Sym sym = Z3.Z3_mk_string_symbol(ctx, sym)
      fun ptr_ref () = ref (Ptr.NULL())
    in
    let
      val head_tail = vec[Sym "car", Sym "cdr"]
      (* build a forest *)
      val nil1_con  = Z3.Z3_mk_constructor(ctx
                                      , Sym "nil1", Sym "is_nil1"
                                      , empty(), empty(), empty())
      val cons1_con = Z3.Z3_mk_constructor(ctx
                                      , Sym "cons1", Sym "is_cons1"
                                      , head_tail
                                      , vec[NONE, NONE]
                                      , vec[0w1, 0w0])
      val constructors1 = vec[nil1_con, cons1_con]

      (* build a tree *)
      val nil2_con  = Z3.Z3_mk_constructor(ctx
                                      , Sym "nil2", Sym "is_nil2"
                                      , empty(), empty(), empty())
      val cons2_con = Z3.Z3_mk_constructor(ctx
                                      , Sym "cons1", Sym "is_cons1"
                                      , head_tail
                                      , vec[NONE, NONE]
                             (* both branches of a tree are forests *)
                                      , vec[0w0, 0w0])
      val constructors2 = vec[nil2_con, cons2_con]
      val clists = Array.fromList[
                      Z3.Z3_mk_constructor_list(ctx, constructors1)
                    , Z3.Z3_mk_constructor_list(ctx, constructors2)
                   ]
      (* HACK: construct bool sort as dummy *)
      val sorts = Array.fromList[ Z3.Z3_mk_bool_sort ctx
                                , Z3.Z3_mk_bool_sort ctx ]
      val () = Z3.Z3_mk_datatypes(ctx
                              , vec[Sym "forest", Sym "tree"]
                              , sorts
                              , clists)
      val forest = Array.sub (sorts, 0)
      val tree   = Array.sub (sorts, 1)

      val ( nil1_decl,  is_nil1_decl) = (ptr_ref(), ptr_ref())
      val (cons1_decl, is_cons1_decl) = (ptr_ref(), ptr_ref())
      val cons_accessors = Array.fromList[Ptr.NULL(), Ptr.NULL()]
      val () = Z3.Z3_query_constructor(ctx
                                   , nil1_con, nil1_decl, is_nil1_decl, Array.fromList[])
      val () = Z3.Z3_query_constructor(ctx
                                   , cons1_con, cons1_decl, is_cons1_decl, cons_accessors)
      val ( nil2_decl,  is_nil2_decl) = (ptr_ref(), ptr_ref())
      val (cons2_decl, is_cons2_decl) = (ptr_ref(), ptr_ref())
      val () = Z3.Z3_query_constructor(ctx
                                   , nil2_con, nil2_decl, is_nil2_decl, Array.fromList[])
      val () = Z3.Z3_query_constructor(ctx
                                   , cons2_con, cons2_decl, is_cons2_decl, cons_accessors)
      val () = app (fn ctor => Z3.Z3_del_constructor(ctx, ctor))
                   [nil1_con, cons1_con, nil2_con, cons2_con]

      val nil1 = Z3.Z3_mk_app(ctx, !nil1_decl, vec[])
      val nil2 = Z3.Z3_mk_app(ctx, !nil2_decl, vec[])
      fun Cons1 x xs = mk_binary_app ctx (!cons1_decl) x xs
      fun Cons2 x xs = mk_binary_app ctx (!cons2_decl) x xs
      val f1 = Cons1 nil2 nil1
      val t1 = Cons2 nil1 nil1
      val t2 = Cons2   f1 nil1
      val t3 = Cons2   f1   f1
      val t4 = Cons2 nil1   f1
      val f2 = Cons1   t1 nil1
      val f3 = Cons1   t1   f1
    in
      (* nil != cons(nil,nil) *)
      prove ctx (nil1 != f1) Z3.Z3_TRUE;
      prove ctx (nil2 != t1) Z3.Z3_TRUE;
    let
      (* cons(x,u) = cons(x,v) => u = v *)
      val u = mk_var ctx "u" forest
      val v = mk_var ctx "v" forest
      val x = mk_var ctx "x" tree
      val y = mk_var ctx "y" tree
      val l1 = Cons1 x u
      val l2 = Cons1 y v
    in
      prove ctx ((l1 == l2) ==> (u == v)) Z3.Z3_TRUE;
      prove ctx ((l1 == l2) ==> (x == y)) Z3.Z3_TRUE;
    let
      (* is_nil(u) or is_cons(u) *)
      val ors = vec[
                  Z3.Z3_mk_app(ctx,  !is_nil1_decl, vec[u]),
                  Z3.Z3_mk_app(ctx, !is_cons1_decl, vec[u])
                ]
    in
      prove ctx (Z3.Z3_mk_or(ctx, ors)) Z3.Z3_TRUE;
      (* occurs check u != cons(x,u) *)
      prove ctx (u != l1) Z3.Z3_TRUE
    end end end end)

   (**
    * Create a binary tree datatype of the form
    *  BinTree ::=   nil 
    *              | node(value : Int, left : BinTree, right : BinTree)
    *)
  fun binary_tree_example () =
    with_context (fn ctx =>
    let
      infix  ==  !=
      infixr ==>
      fun p ==> q = Z3.Z3_mk_implies(ctx, p, q)
      fun p ==  q = Z3.Z3_mk_eq(ctx, p, q)
      fun p !=  q = Z3.Z3_mk_not(ctx, Z3.Z3_mk_eq(ctx, p, q))

      fun Sym sym = Z3.Z3_mk_string_symbol(ctx, sym)
      val vec = Vector.fromList
      fun empty () = vec[]
      fun ptr_ref () = ref (Ptr.NULL())
    in
    let
      val node_accessor_names     = vec[Sym "value", Sym "left", Sym "right"]
      val node_accessor_sorts     = vec[SOME(Z3.Z3_mk_int_sort ctx), NONE, NONE]
      val node_accessor_sort_refs = vec[0w0, 0w0, 0w0]
      (* nil_con and node_con are auxiliary datastructures used to create the new recursive datatype BinTree *)
      val nil_con  = Z3.Z3_mk_constructor(ctx
                                      , Sym "nil", Sym "is-nil"
                                      , empty(), empty(), empty())
      val node_con = Z3.Z3_mk_constructor(ctx
                                      , Sym "node", Sym "is-cons"
                                      , node_accessor_names
                                      , node_accessor_sorts
                                      , node_accessor_sort_refs)
      val constructors = Array.fromList[nil_con, node_con]
      (* create the new recursive datatype *)
      val cell = Z3.Z3_mk_datatype(ctx, Sym "BinTree", constructors)

      val ( nil_decl,  is_nil_decl) = (ptr_ref(), ptr_ref())
      val () = Z3.Z3_query_constructor(ctx
                                   , nil_con, nil_decl, is_nil_decl, Array.fromList[])
      val (node_decl, is_node_decl) = (ptr_ref(), ptr_ref())
      val node_accessors = Array.fromList[Ptr.NULL(), Ptr.NULL(), Ptr.NULL()]
      val () = Z3.Z3_query_constructor(ctx
                                   , node_con, node_decl, is_node_decl, node_accessors)
      val value_decl = Array.sub(node_accessors, 0)
      val left_decl  = Array.sub(node_accessors, 1)
      val right_decl = Array.sub(node_accessors, 2)
      (* delete auxiliary/helper structures *)
      val () = app (fn x=> Z3.Z3_del_constructor(ctx, x)) [nil_con, node_con]
    in
      (* small example using the recursive datatype BinTree *)
    let
      (* create nil *)
      val Nil = Z3.Z3_mk_app(ctx, !nil_decl, empty())
      fun Node v l r = Z3.Z3_mk_app(ctx, !node_decl, vec[v, l, r])
      val node1 = Node (mk_int ctx 10)   Nil   Nil
      val node2 = Node (mk_int ctx 30) node1   Nil
      val node3 = Node (mk_int ctx 20) node2 node1
      fun Left  u = mk_unary_app ctx left_decl  u
      fun Right u = mk_unary_app ctx right_decl u
    in
      (* prove that nil != node1 *)
      prove ctx (Nil != node1) Z3.Z3_TRUE;
      (* prove that nil = left(node1) *)
      prove ctx (Nil == Left node1) Z3.Z3_TRUE;
      (* prove that node1 = right(node3) *)
      prove ctx (node1 == Right node3) Z3.Z3_TRUE;
      (* prove that !is-nil(node2) *)
      prove ctx (Z3.Z3_mk_not(ctx
                    , mk_unary_app ctx (!is_nil_decl) node2)) Z3.Z3_TRUE;
      (* prove that value(node2) >= 0 *)
      prove ctx (Z3.Z3_mk_ge(ctx
                    , mk_unary_app ctx value_decl node2
                    , mk_int ctx 0)) Z3.Z3_TRUE
    end end end)

  (**
   * Create an enumeration data type
   *)
  fun enum_example () =
    with_context (fn ctx =>
    let
      infix  ==  !=
      infixr ==>
      fun p ==> q = Z3.Z3_mk_implies(ctx, p, q)
      fun p ==  q = Z3.Z3_mk_eq(ctx, p, q)
      fun p !=  q = Z3.Z3_mk_not(ctx, Z3.Z3_mk_eq(ctx, p, q))

      fun Sym sym = Z3.Z3_mk_string_symbol(ctx, sym)
      fun ptr_ref () = ref (Ptr.NULL())
      val vec = Vector.fromList
      fun empty () = vec[]
    in
      (* sample begin *)
    let
      val enum_consts  = Array.fromList[Ptr.NULL(), Ptr.NULL(), Ptr.NULL()]
      val enum_testers = Array.fromList[Ptr.NULL(), Ptr.NULL(), Ptr.NULL()]
      val fruit = Z3.Z3_mk_enumeration_sort(ctx
                                        , Sym "fruit"
                                        , vec (map Sym ["apple", "banana", "orange"])
                                        , enum_consts
                                        , enum_testers)
    in
      Array.app (fn e=> print(concat[Z3.Z3_func_decl_to_string(ctx, e), "\n"])) enum_consts;
      Array.app (fn e=> print(concat[Z3.Z3_func_decl_to_string(ctx, e), "\n"])) enum_testers;

    let
      val apple  = Z3.Z3_mk_app (ctx, Array.sub(enum_consts,0), empty())
      val banana = Z3.Z3_mk_app (ctx, Array.sub(enum_consts,1), empty())
      val orange = Z3.Z3_mk_app (ctx, Array.sub(enum_consts,2), empty())
    in
      (* Apples are differenct from oranges *)
      prove ctx (apple != orange) Z3.Z3_TRUE;
      (* Apples pass the apple test *)
      prove ctx (Z3.Z3_mk_app(ctx, Array.sub(enum_testers,0), vec[apple])) Z3.Z3_TRUE;
      (* Oranges fail the apple test *)
      prove ctx (Z3.Z3_mk_app(ctx, Array.sub(enum_testers,0), vec[orange])) Z3.Z3_FALSE;
      prove ctx (Z3.Z3_mk_not(ctx
                  , Z3.Z3_mk_app(ctx
                    , Array.sub(enum_testers,0), vec[orange]))) Z3.Z3_TRUE;

    let
      val fruity = mk_var ctx "fruity" fruit
      (* If something is fruity, then it is an apple, banana, or orange *)
      val ors = vec[fruity == apple
                   ,fruity == banana
                   ,fruity == orange]
    in
      prove ctx (Z3.Z3_mk_or(ctx, ors)) Z3.Z3_TRUE
    end end end end)

  fun unsat_core_and_proof_example () =
    using mk_proof_context
          Z3.Z3_del_context
          (fn ctx =>
    let
      fun <&> ps = Z3.Z3_mk_and(ctx, ps)
      fun <|> ps = Z3.Z3_mk_or (ctx, ps)
      fun Not p  = Z3.Z3_mk_not(ctx, p)

      val vec = Vector.fromList
      fun Bool id = mk_bool_var ctx id

      val (pa,pb,pc,pd) = (Bool "PredA", Bool "PredB", Bool "PredC", Bool "PredD")
      val (p1,p2,p3,p4) = (Bool "P1", Bool "P2", Bool "P3", Bool "P4")

      val f1 = <&> (vec[pa, pb, pc])
      val f2 = <&> (vec[pa, Not pb, pc])
      val f3 = <|> (vec[Not pa, Not pc])
      val f4 = <&> (vec[pd])
    in
      D.Z3_assert_cnstr(ctx, <|> (vec[f1, p1])); (* g1 *)
      D.Z3_assert_cnstr(ctx, <|> (vec[f2, p2])); (* g2 *)
      D.Z3_assert_cnstr(ctx, <|> (vec[f3, p3])); (* g3 *)
      D.Z3_assert_cnstr(ctx, <|> (vec[f4, p4])); (* g4 *)

    let
      val assumptions = vec[Not p1, Not p2, Not p3, Not p4]
      val m : Z3.Z3_model ref = ref (Ptr.NULL())
      val proof : Z3.Z3_ast ref = ref (Ptr.NULL())
      val core_size = ref 0w4
      val core = Array.tabulate(Vector.length assumptions, fn _=> Ptr.NULL())
    in
      case D.Z3_check_assumptions(ctx
                                 , assumptions
                                 , m
                                 , proof
                                 , core_size
                                 , core)
        of Z3.Z3_lbool.Z3_L_FALSE =>
             (print(concat
                   ["unsat\n"
                   ,"proof: ", Z3.Z3_ast_to_string(ctx, !proof), "\n"]);
              print "\ncore:\n";
              for 0 (fn i=> (Word.fromInt i) < !core_size) (fn i=>i+1) (fn i=>
                print (Z3.Z3_ast_to_string(ctx, Array.sub(core,i))^"\n")
              );
              print "\n")
         | Z3.Z3_lbool.Z3_L_UNDEF =>
             (print(concat[
                    "unknown\n"
                   ,"potential model:\n"]);
              Display.model ctx TextIO.stdOut (!m))
         | Z3.Z3_lbool.Z3_L_TRUE =>
             (print "sat\n";
              Display.model ctx TextIO.stdOut (!m));
      if not (Ptr.isNull (!m)) then (
        D.Z3_del_model (ctx, !m);
        m := Ptr.NULL()
      ) else ()
    end end)

  structure Z3_ext_context =
  struct
    val MAX_RETRACTABLE_ASSERTIONS = ref 1024
    type t =
      { context             : Z3.Z3_context
      , answer_literals     : Z3.Z3_ast array
      , retracted           : Z3.Z3_bool array
      , num_answer_literals : word ref
      }

    fun mk () : t =
      { context             = mk_context ()
      , answer_literals     = Array.array(!MAX_RETRACTABLE_ASSERTIONS, Ptr.NULL())
      , retracted           = Array.array(!MAX_RETRACTABLE_ASSERTIONS, Z3.Z3_FALSE)
      , num_answer_literals = ref 0w0
      }

    fun delete ({context,...}:t) =
      Z3.Z3_del_context context

    fun assert_retractable_cnstr {context
                                 ,answer_literals
                                 ,num_answer_literals
                                 ,retracted} c =
    let
      val ty      = Z3.Z3_mk_bool_sort context
      val ans_lit = Z3.Z3_mk_fresh_const (context, "k", ty)
      val result  = !num_answer_literals
    in
      Array.update(answer_literals, Word.toInt result, ans_lit);
      Array.update(retracted, Word.toInt result, Z3.Z3_FALSE);
      num_answer_literals := (!num_answer_literals) + 0w1;
      D.Z3_assert_cnstr(context
                       , Z3.Z3_mk_or(context
                       , Vector.fromList[c, Z3.Z3_mk_not(context, ans_lit)]));
      result
    end

    fun check ({ context
               , answer_literals
               , num_answer_literals
               , retracted }:t) =
    let
      val assumptions = Array.array(Word.toInt (!num_answer_literals), Ptr.NULL())
      val num_assumptions = ref 0
    in
      for 0 (fn i=> i < Word.toInt (!num_answer_literals)) (fn i=>i+1) (fn i=>
        if Array.sub(retracted, i) = Z3.Z3_FALSE
        then (
          Array.update(assumptions, !num_assumptions, Array.sub(answer_literals,i));
          num_assumptions := (!num_assumptions) + 1
        ) else ());
      let
        fun ptr_ref () = ref (Ptr.NULL())
        val core_size = ref 0w0
        val core = Array.tabulate(Array.length assumptions, fn _=> Ptr.NULL())
        val assumptions' = Vector.tabulate(!num_assumptions, fn i=>
                             Array.sub(assumptions, i))
        val result = D.Z3_check_assumptions( context
                                           , assumptions'
                                           , ptr_ref()
                                           , ptr_ref()
                                           , core_size
                                           , core )
        fun for' n = for 0w0 (fn i=> i<n) (fn i=>i+0w1)
        val sub = Array.sub
      in
        if result = Z3.Z3_lbool.Z3_L_FALSE
        then (
          print "unsat core: ";
          for' (!core_size) (fn i=>
            (let val j = ref 0
                 exception Break
             in
              (while !j < Word.toInt (!num_answer_literals) do (
                 if sub(core, Word.toInt i) = sub(answer_literals, (!j))
                 then (print(concat[Int.toString (!j), " "]);
                       raise Break)
                 else ();
                 j := (!j) + 1
               )
              ) handle Break => ();
              check_cond (fn()=> !j = Word.toInt (!num_answer_literals))
                (SOME "bug in Z3, the core contains something that is not an assumption.")
             end));
          print "\n"
        ) else ();
        result
      end
    end

  end (* Z3_ext_context *)

  fun retract_cnstr ctx id =
    (check_cond (fn()=> id >= !(#num_answer_literals ctx))
                (SOME "invalid constraint id.");
     Array.update(#retracted ctx, Word.toInt id, Z3.Z3_TRUE))

  fun reassert_cnstr ctx id =
    (check_cond (fn()=> id >= !(#num_answer_literals ctx))
                (SOME "invalid constraint id.");
     Array.update(#retracted ctx, Word.toInt id, Z3.Z3_FALSE))

  local structure Ext = Z3_ext_context in
  fun incremental_example1 () =
    using Z3_ext_context.mk
          Z3_ext_context.delete
    (fn ext_ctx =>
    let
      val ctx = #context ext_ctx
      val x = mk_int_var ctx "x"
      val y = mk_int_var ctx "y"
      val z = mk_int_var ctx "z"
      val two = mk_int ctx 2
      val one = mk_int ctx 1

      (* assert x < y *)
      val c1 = Ext.assert_retractable_cnstr ext_ctx (Z3.Z3_mk_lt(ctx, x, y))
      (* assert x = z *)
      val c2 = Ext.assert_retractable_cnstr ext_ctx (Z3.Z3_mk_eq(ctx, x, z))
      (* assert x > 2 *)
      val c3 = Ext.assert_retractable_cnstr ext_ctx (Z3.Z3_mk_gt(ctx, x, two))
      (* assert y < 1 *)
      val c4 = Ext.assert_retractable_cnstr ext_ctx (Z3.Z3_mk_lt(ctx, y, one))

      fun check_bug f = check_cond f (SOME "bug in Z3")
    in
      check_bug (fn()=> Ext.check ext_ctx <> Z3.Z3_lbool.Z3_L_FALSE);
      print "unsat\n";

      retract_cnstr ext_ctx c4;
      check_bug (fn()=> Ext.check ext_ctx <> Z3.Z3_lbool.Z3_L_TRUE );
      print "sat\n";

      reassert_cnstr ext_ctx c4;
      check_bug (fn()=> Ext.check ext_ctx <> Z3.Z3_lbool.Z3_L_FALSE);
      print "unsat\n";

      retract_cnstr ext_ctx c2;
      check_bug (fn()=> Ext.check ext_ctx <> Z3.Z3_lbool.Z3_L_FALSE);
      print "unsat\n";

      retract_cnstr ext_ctx c3;
      check_bug (fn()=> Ext.check ext_ctx <> Z3.Z3_lbool.Z3_L_TRUE );
      print "sat\n"
    end)
  end (* local *)

  fun reference_counter_example () =
    with_context (fn ctx =>
    let
      val ty = Z3.Z3_mk_bool_sort ctx
      val () = Z3.Z3_inc_ref(ctx, Z3.Z3_sort_to_ast(ctx, ty))
      fun Sym sym = Z3.Z3_mk_string_symbol (ctx, sym)
      val x  = Z3.Z3_mk_const (ctx, Sym "x", ty)
    in
      Z3.Z3_inc_ref(ctx, x);
    let
      val y  = Z3.Z3_mk_const (ctx, Sym "y", ty)
    in
      Z3.Z3_inc_ref(ctx, y);
      (* ty is not needed anymore *)
      Z3.Z3_dec_ref(ctx, Z3.Z3_sort_to_ast(ctx, ty));
    let
      val x_xor_y = Z3.Z3_mk_xor(ctx, x, y)
    in
      Z3.Z3_inc_ref(ctx, x_xor_y);
      (* x and y are not needed anymore. *)
      Z3.Z3_dec_ref(ctx, x);
      Z3.Z3_dec_ref(ctx, y);
      D.Z3_assert_cnstr(ctx, x_xor_y);
      (* x_xor_y is not needed anymore. *)
      Z3.Z3_dec_ref(ctx, x_xor_y);

      print "model for: x xor y\n";
      check ctx Z3.Z3_lbool.Z3_L_TRUE;

      (* Test push & pop *)
      D.Z3_push ctx;
      D.Z3_pop(ctx, 0w1)
    end end end)

  fun smt2parser_example () =
    with_context (fn ctx =>
    let
      fun empty () = Vector.fromList[]
      val fs = Z3.Z3_parse_smtlib2_string(
                   ctx
                 , concat[
                     "(declare-fun a () (_ BitVec 8))",
                     "(assert (bvuge a #x10))",
                     "(assert (bvule a #xf0))"
                   ]
                 , empty(), empty()
                 , empty(), empty())
    in
      print(concat["formulas: "
                  , Z3.Z3_ast_to_string(ctx, fs), "\n"])
    end)

  fun substitute_example () =
    with_context (fn ctx =>
    let
      open Z3
      val vec = Vector.fromList
      val int_ty = Z3_mk_int_sort ctx
      val a = mk_int_var ctx "a"
      val b = mk_int_var ctx "b"
      fun Sym sym = Z3_mk_string_symbol(ctx, sym)
      val f = Z3_mk_func_decl(ctx
                , Sym "f"
                , vec[int_ty, int_ty], int_ty)
      val g = Z3_mk_func_decl(ctx
                , Sym "g"
                , vec[int_ty], int_ty)
      val fab = Z3_mk_app(ctx, f, vec[a,b])
      val ga  = Z3_mk_app(ctx, g, vec[a])
      val ffabga = Z3_mk_app(ctx, f, vec[fab, ga])
    in
      (* Replace b -> 0, g(a) -> 1 in f(f(a, b), g(a)) *)
    let
      val zero = Z3_mk_numeral(ctx, "0", int_ty)
      val one  = Z3_mk_numeral(ctx, "1", int_ty)
      val from = vec[b, ga]
      val to   = vec[zero, one]
      val r    = Z3_substitute(ctx, ffabga, from, to)
    in
      (* Display r *)
      print(concat["substitution result: "
                    , Z3_ast_to_string(ctx, r), "\n"])
    end
    end)

  fun substitute_vars_example () =
    with_context (fn ctx =>
    let
      open Z3
      val vec = Vector.fromList
      fun Sym sym = Z3_mk_string_symbol(ctx, sym)
      val int_ty = Z3_mk_int_sort ctx
      val x0 = Z3_mk_bound (ctx, 0w0, int_ty)
      val x1 = Z3_mk_bound (ctx, 0w1, int_ty)
      val f = Z3_mk_func_decl(ctx
                            , Sym "f"
                            , vec[int_ty, int_ty], int_ty)
      val g = Z3_mk_func_decl(ctx
                            , Sym "g"
                            , vec[int_ty], int_ty)
      (* f x0 x1 *)
      val f01   = Z3_mk_app(ctx, f, vec[x0, x1])
      (* f (f x0 x1) x0 *)
      val ff010 = Z3_mk_app(ctx, f, vec[f01, x0])
      val a = mk_int_var ctx "a"
      val b = mk_int_var ctx "b"
      val gb = Z3_mk_app(ctx, g, vec[b])
      val r = Z3_substitute_vars(ctx, ff010, vec[a, gb])
    in
      print(concat["substitution result: "
                  , Z3_ast_to_string(ctx, r), "\n"])
    end)

  val sample_cases =
     [ (display_version, "display_version")
     , (simple_example, "simple_example")
     , (demorgan, "DeMorgan")
     , (find_model_example1, "find_model_example1")
     , (find_model_example2, "find_model_example2")
     , (prove_example1, "prove_example1")
     , (prove_example2, "prove_example2")
     , (push_pop_example1, "push_pop_example1")
     , (quantifier_example1, "quantifier_example1")
     , (array_example1, "array_example1")
     , (array_example2, "array_example2")
     , (array_example3, "array_example3")
     , (tuple_example1, "tuple_example1")
     , (bitvector_example1, "bitvector_example1")
     , (bitvector_example2, "bitvector_example2")
     , (eval_example1, "eval_example1")
     , (two_contexts_example1, "two_contexts_example1")
     , (error_code_example1, "error_code_example1")
     , (error_code_example2, "error_code_example2")
     , (parser_example1, "parser_example1")
     , (parser_example2, "parser_example2")
     , (parser_example3, "parser_example3")
     , (parser_example4, "parser_example4")
     , (parser_example5, "parser_example5")
     , (numeral_example, "numeral_example")
     , (ite_example, "ite_example")
     , (list_example, "list_example")
     , (tree_example, "tree_example")
     , (forest_example, "forest_example")
     , (binary_tree_example, "binary_tree_example")
     , (enum_example, "enum_example")
     , (unsat_core_and_proof_example, "unsat_core_and_proof_example")
     , (incremental_example1, "incremental_example1")
     , (reference_counter_example, "reference_counter_example")
     , (smt2parser_example, "smt2parser_example")
     , (substitute_example, "substitute_example")
     , (substitute_vars_example, "substitute_vars_example")
     ]

  fun call_case (f, name) =
    (print(concat["\n", name, "\n"]);
     LOG_MSG name;
     f())

  fun open_log file =
    if Z3.Z3_open_log file
    then ()
    else raise Fail (concat["Z3_open_log: ", file])

  fun main (name, args) =
    (case args
       of "-l"::_ => (LOG_Z3_CALLS := true; open_log "z3.log")
        | _       => ();
     app call_case sample_cases;
     call_case (tutorial_sample, "tutorial_sample");
     OS.Process.success
    )
    handle exn => (print(concat["main:uncaught exception[", exnMessage exn, "]\n"]);
                   OS.Process.failure)
end
val _ = Main.main (CommandLine.name(), CommandLine.arguments())

