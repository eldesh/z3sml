
structure Z3_bool =
struct
  datatype t = datatype Bool.bool
  val Z3_TRUE  = true
  val Z3_FALSE = false

  fun toInt true = 1
    | toInt _    = 0

  fun fromInt 0 = false
    | fromInt _ = true
end


