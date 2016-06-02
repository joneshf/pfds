structure CustomStack : STACK =
struct
  datatype 'a Stack = Nil | Cons of 'a * 'a Stack

  val empty = Nil

  fun isEmpty Nil = true
    | isEmpty _ = false

  val cons = Cons

  fun head Nil = raise EMPTY
    | head (Cons (x, _)) = x

  fun tail Nil = raise EMPTY
    | tail (Cons (_, s)) = s
end
