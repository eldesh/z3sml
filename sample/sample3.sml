
(**
 * solve sudoku puzzle by SMT solver
 *)
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

  fun mk_var ctx name ty =
    Z3_mk_const (ctx, Z3_mk_string_symbol (ctx, name), ty)

  fun int_var ctx name =
    mk_var ctx name (Z3_mk_int_sort ctx)
in
  fun solve () =
    with_context (fn ctx =>
    let
      fun Var id = int_var ctx id

      fun Int v =
        Z3_mk_int (ctx, v, Z3_mk_int_sort ctx)

      infix 4 == <> >= <=
      fun p == q = Z3_mk_eq (ctx, p, q)
      fun p <> q = Z3_mk_not (ctx, p == q)
      fun p <= q = Z3_mk_le (ctx, p, q)
      fun p >= q = Z3_mk_ge (ctx, p, q)

      fun && xs = Z3_mk_and (ctx, Vector.fromList xs)

      fun assert p = D.Z3_assert_cnstr (ctx, p)

      val x11 = Var "v11"
      val x12 = Var "v12"
      val x13 = Var "v13"
      val x14 = Var "v14"
      val x21 = Var "v21"
      val x22 = Var "v22"
      val x23 = Var "v23"
      val x24 = Var "v24"
      val x31 = Var "v31"
      val x32 = Var "v32"
      val x33 = Var "v33"
      val x34 = Var "v34"
      val x41 = Var "v41"
      val x42 = Var "v42"
      val x43 = Var "v43"
      val x44 = Var "v44"

    in
      (* domain *)
      assert (&& [(Int 1 <= x11), (x11 <= Int 4)]);
      assert (&& [(Int 1 <= x12), (x12 <= Int 4)]);
      assert (&& [(Int 1 <= x13), (x13 <= Int 4)]);
      assert (&& [(Int 1 <= x14), (x14 <= Int 4)]);
      assert (&& [(Int 1 <= x21), (x21 <= Int 4)]);
      assert (&& [(Int 1 <= x22), (x22 <= Int 4)]);
      assert (&& [(Int 1 <= x23), (x23 <= Int 4)]);
      assert (&& [(Int 1 <= x24), (x24 <= Int 4)]);
      assert (&& [(Int 1 <= x31), (x31 <= Int 4)]);
      assert (&& [(Int 1 <= x32), (x32 <= Int 4)]);
      assert (&& [(Int 1 <= x33), (x33 <= Int 4)]);
      assert (&& [(Int 1 <= x34), (x34 <= Int 4)]);
      assert (&& [(Int 1 <= x41), (x41 <= Int 4)]);
      assert (&& [(Int 1 <= x42), (x42 <= Int 4)]);
      assert (&& [(Int 1 <= x43), (x43 <= Int 4)]);
      assert (&& [(Int 1 <= x44), (x44 <= Int 4)]);

      (* distinct row *)
      assert (&& [(x11 <> x21), (x11 <> x31), (x11 <> x41), (x21 <> x31), (x21 <> x41), (x31 <> x41)]);
      assert (&& [(x12 <> x22), (x12 <> x32), (x12 <> x42), (x22 <> x32), (x22 <> x42), (x32 <> x42)]);
      assert (&& [(x13 <> x23), (x13 <> x33), (x13 <> x43), (x23 <> x33), (x23 <> x43), (x33 <> x43)]);
      assert (&& [(x14 <> x24), (x14 <> x34), (x14 <> x44), (x24 <> x34), (x24 <> x44), (x34 <> x44)]);

      (* distinct column *)
      assert (&& [(x11 <> x12), (x11 <> x13), (x11 <> x14), (x12 <> x13), (x12 <> x14), (x13 <> x14)]);
      assert (&& [(x21 <> x22), (x21 <> x23), (x21 <> x24), (x22 <> x23), (x22 <> x24), (x23 <> x24)]);
      assert (&& [(x31 <> x32), (x31 <> x33), (x31 <> x34), (x32 <> x33), (x32 <> x34), (x33 <> x34)]);
      assert (&& [(x41 <> x42), (x41 <> x43), (x41 <> x44), (x42 <> x43), (x42 <> x44), (x43 <> x44)]);

      (* distinct 2x2 block *)
      assert (&& [(x11 <> x12), (x11 <> x21), (x11 <> x22), (x12 <> x21), (x12 <> x22), (x21 <> x22)]);
      assert (&& [(x13 <> x14), (x13 <> x23), (x13 <> x24), (x14 <> x23), (x14 <> x24), (x23 <> x24)]);
      assert (&& [(x31 <> x32), (x31 <> x41), (x31 <> x42), (x32 <> x41), (x32 <> x42), (x41 <> x42)]);
      assert (&& [(x33 <> x34), (x33 <> x43), (x33 <> x44), (x34 <> x43), (x34 <> x44), (x43 <> x44)]);

      (* pre assinged values *)

      (**
       *     1   2   3   4
       *   +---+---+---+---+
       * 1 |   |   |   | 4 |
       *   +---+---+---+---+
       * 2 |   |   | 1 | 2 |
       *   +---+---+---+---+
       * 3 |   | 1 | 4 | 3 |
       *   +---+---+---+---+
       * 4 | 4 | 3 | 2 | 1 |
       *   +---+---+---+---+
       *)
      assert (x14 == Int 4);
      assert (x23 == Int 1);
      assert (x24 == Int 2);
      assert (x32 == Int 1);
      assert (x33 == Int 4);
      assert (x34 == Int 3);
      assert (x41 == Int 4);
      assert (x42 == Int 3);
      assert (x43 == Int 2);
      assert (x44 == Int 1);

      check ctx Z3.Z3_lbool.Z3_L_TRUE
    end)

  fun main (name, args) =
    (solve();
     OS.Process.success
    )
end (* local *)
end
val _ = Main.main (CommandLine.name(), CommandLine.arguments())

