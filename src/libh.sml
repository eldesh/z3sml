
structure Library =
struct
  val libz3 = DynamicLink.dlopen "libz3.so"
end

