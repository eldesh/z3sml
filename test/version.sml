
structure Test =
struct
  val supportVersion = (0w4,0w3,0w2,0w0)

  fun version () =
    let
      val (major, minor, build, revision) = (ref 0w0, ref 0w0, ref 0w0, ref 0w0)
    in
      Z3.Z3_get_version (major, minor, build, revision);
      (!major, !minor, !build, !revision)
    end

  fun main (name, argv) =
  let
    val ` = Word.toString
    fun v2s (x,y,z,p) = String.concatWith "." [`x, `y, `z, `p]
    val ver as (x,y,z,p) = version()
  in
    print(concat["binding to z3 v", v2s ver, "\n"]);
    (if supportVersion = ver
     then
       print(concat["supported version!\n"])
     else
       print(concat["not match to supported version v", v2s ver, "\n"]));
    OS.Process.success
  end
  handle exn =>
    (print(concat["Test.main fail with:", exnMessage exn, "\n"]);
     OS.Process.failure)
end
val _ = Test.main(CommandLine.name(), CommandLine.arguments())

