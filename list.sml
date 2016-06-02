structure List : STACK =
struct
  type 'a Stack = 'a list

  val empty = []
  val isEmpty = null
  val cons = op ::
  val head = hd
  val tail = tl
end
