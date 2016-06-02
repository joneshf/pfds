(* Ex. 2.1 *)
fun suffixes [] = [[]]
  | suffixes (x::xs) = (x::xs) :: suffixes xs

(*
before
xs -> [1| ] -> [2| ] -> [3| ] -> [4|*]

after
ys -> [ | ] -> [ | ] -> [ | ] -> [ | ] -> [ |*]
       |        |        |        |        |
       V        V        V        V        V
       xs -> [1| ] -> [2| ] -> [3| ] -> [4|*]
*)

(* Ex. 2.2 *)
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
    | member (x, set as T (l, y, r)) =
      memberEfficient (x, y, set)
  and memberEfficient (x, y, E) = Element.eq (x, y)
    | memberEfficient (x, y, T (l, z, r)) =
      if Element.leq (x, z) then
        memberEfficient (x, z, l)
      else
        memberEfficient (x, y, r)
end

(* Ex. 2.3 *)
functor UnbalancedSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T
  datatype Tree = E | T of Tree * Elem * Tree
  type Set = Tree

  exception Exists

  val empty = E

  fun insert (x, set) =
    insertException (x, set)
      handle Exists => set
  and insertException (x, E) = T (E, x, E)
    | insertException (x, T (l, y, r)) =
      if Element.lt (x, y) then
        T (insert (x, l), y, r)
      else if Element.lt (y, x) then
        T (l, y, insert (x, r))
      else
        raise Exists

  fun member (_, E) = false
    | member (x, T (l, y, r)) =
      if Element.lt (x, y) then
        member (x, l)
      else if Element.lt (y, x) then
        member (x, r)
      else
        true
end

(* Ex. 2.4 *)
functor UnbalancedSet (Element : ORDERED) : SET =
struct
  type Elem = Element.T
  datatype Tree = E | T of Tree * Elem * Tree
  type Set = Tree

  exception Exists

  val empty = E

  fun insert (x, E) = T (E, x, E)
    | insert (x, set as T (l, y, r)) =
      insertEfficientException (x, y, set)
        handle Exists => set
  and insertEfficientException (x, y, E) =
    if Element.eq (x, y) then
      raise Exists
    else
      T (E, x, E)
    | insertEfficientException (x, y, T (l, z, r)) =
      if Element.leq (x, z) then
        T (insertEfficientException (x, z, l), z, r)
      else
        T (l, z, insertEfficientException (x, y, r))

  fun member (_, E) = false
    | member (x, T (l, y, r)) =
      if Element.lt (x, y) then
        member (x, l)
      else if Element.lt (y, x) then
        member (x, r)
      else
        true
end

(* Ex. 2.5(a) *)
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

  fun complete (x, d) =
    if d <= 0 then
      E
    else
      let
        val set = complete (x, d - 1)
      in
        T (set, x, set)
      end
end

(* Ex. 2.5(b) *)
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

  fun balanced (x, size) =
    if size <= 0 then
      E
    else if size = 1 then
      T (E, x, E)
    else if odd size then
      let
        val set = balanced (x, half size)
      in
        T (set, x, set)
      end
    else
      T (balanced (x, half size - 1), x, balanced (x, half size))
  and odd size = size mod 2 = 1
  and half size = size div 2
end

(* Ex. 2.6 *)
functor UnbalancedFiniteMap (K : ORDERED) : FINITEMAP =
struct
  type Key = K.T
  datatype 'a Tree = E | T of 'a Tree * Key * 'a * 'a Tree
  type 'a Map = 'a Tree

  exception NOTFOUND

  val empty = E
  fun bind (k, v, E) = T (E, k, v, E)
    | bind (k1, v1, map as T (l, k2, v2, r)) =
      if K.lt (k1, k2) then
        T (bind (k1, v1, l), k2, v2, r)
      else if K.lt (k2, k1) then
        T (l, k2, v2, bind (k1, v1, r))
      else
        map
  fun lookup (k, E) = raise NOTFOUND
    | lookup (k1, T (l, k2, v, r)) =
      if K.eq (k1, k2) then
        v
      else if K.lt (k1, k2) then
        lookup (k1, l)
      else
        lookup (k1, r)
end
