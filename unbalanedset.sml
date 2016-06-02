functor UnbalancedSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T
  datatype Tree = E | T of Tree * Elem * Tree
  type Set = Tree

  val empty = E

  fun insert (x, E) = T (E, x, E)
    | insert (x, set as T (l, y, r)) =
      if Element.lt (x, y) then
        T (insert (x, l), y, r)
      else if Element.lt (y, x) then
        T (l, y, insert (x, r))
      else
        set

  fun member (_, E) = false
    | member (x, T (l, y, r)) =
      if Element.lt (x, y) then
        member (x, l)
      else if Element.lt (y, x) then
        member (x, r)
      else
        true
end
