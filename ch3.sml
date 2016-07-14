(*
3.1

Take n = 0.
Then we want to show the right spine has at most floor(log(0 + 1)) elements.

floor(log(0 + 1))
  = floor(log(1))
  = floor(0)
  = 0

And since n = 0, there are no elements, and the right spine contains 0 elements.
So the right spine has no more than floor(log(0 + 1)) elements.

Take n = 1.
Then we want to show the right spine has at most floor(log(1 + 1)) elements.

floor(log(1 + 1))
  = floor(log(2))
  = floor(1)
  = 1
  > 0

Since n = 1, there are no children of this node.
So the right spine contains 0 elements, and 1 > 0.
Thus, the right spine has at most floor(log(1 + 1)) elements.

Assume the right side of a leftist heap of size n contains at most
floor(log(n + 1)) elements.
We want to show that the right side of a leftist heap of size n + 1 contains
at most floor(log((n + 1) + 1)) elements.

floor(log((n + 1) + 1))
  = floor(log(n + 2))
...

*)

functor LeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  val empty = E
  fun isEmpty E = true
    | isEmpty _ = false

  fun rank E = 0
    | rank (T (r, _, _, _)) = r

  fun makeT (x, a, b) =
    if rank a >= rank b then
      T (rank b + 1, x, a, b)
    else
      T (rank a + 1, x, b, a)

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (_, x, a1, b1), h2 as T (_, y, a2, b2)) =
      if Elem.leq (x, y) then
        makeT (x, a1, merge (b1, h2))
      else
        makeT (y, a2, merge (h1, b2))

  fun insert (x, h) = merge (T (1, x, E, E), h)

  fun findMin E = raise EMPTY
    | findMin (T (_, x, _, _)) = x

  fun deleteMin E = raise EMPTY
    | deleteMin (T (_, _, a, b)) = merge (a, b)
end

(* Exercise 3.2 *)
functor LeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  val empty = E
  fun isEmpty E = true
    | isEmpty _ = false

  fun rank E = 0
    | rank (T (r, _, _, _)) = r

  fun makeT (x, a, b) =
    if rank a >= rank b then
      T (rank b + 1, x, a, b)
    else
      T (rank a + 1, x, b, a)

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (_, x, a1, b1), h2 as T (_, y, a2, b2)) =
      if Elem.leq (x, y) then
        makeT (x, a1, merge (b1, h2))
      else
        makeT (y, a2, merge (h1, b2))

  fun insert (x, E) = T (1, x, E, E)
    | insert (x, T (_, y, a, b)) =
      if Elem.leq (x, y) then
        makeT (x, a, insert (y, b))
      else
        makeT (y, a, insert (x, b))

  fun findMin E = raise EMPTY
    | findMin (T (_, x, _, _)) = x

  fun deleteMin E = raise EMPTY
    | deleteMin (T (_, _, a, b)) = merge (a, b)
end

(* Exercise 3.3 *)
functor LeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  val empty = E
  fun isEmpty E = true
    | isEmpty _ = false

  fun rank E = 0
    | rank (T (r, _, _, _)) = r

  fun makeT (x, a, b) =
    if rank a >= rank b then
      T (rank b + 1, x, a, b)
    else
      T (rank a + 1, x, b, a)

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (_, x, a1, b1), h2 as T (_, y, a2, b2)) =
      if Elem.leq (x, y) then
        makeT (x, a1, merge (b1, h2))
      else
        makeT (y, a2, merge (h1, b2))

  fun insert (x, E) = T (1, x, E, E)
    | insert (x, T (_, y, a, b)) =
      if Elem.leq (x, y) then
        makeT (x, a, insert (y, b))
      else
        makeT (y, a, insert (x, b))

  fun findMin E = raise EMPTY
    | findMin (T (_, x, _, _)) = x

  fun deleteMin E = raise EMPTY
    | deleteMin (T (_, _, a, b)) = merge (a, b)

  fun singleton x = insert (x, E)

  fun pairs _ [] = []
    | pairs _ [x] = [x]
    | pairs f (x::y::zs) = f (x, y) :: pairs f zs

  fun mergePairs [] = empty
    | mergePairs [x] = x
    | mergePairs xs = mergePairs (pairs merge xs)

  fun fromList xs =
    mergePairs (map singleton xs)
end

(* Exercise 3.4 *)
functor WeightBiasedLeftistHeap (Element : ORDERED) : HEAP =
struct
  structure Elem = Element

  datatype Heap = E | T of int * Elem.T * Heap * Heap

  val empty = E
  fun isEmpty E = true
    | isEmpty _ = false

  fun size E = 0
    | size (T (s, _, _, _)) = s

  fun makeT (x, a, b) =
    if size a >= size b then
      T (size a + size b + 1, x, a, b)
    else
      T (size a + size b + 1, x, b, a)

  fun merge (h, E) = h
    | merge (E, h) = h
    | merge (h1 as T (s1, x, a1, b1), h2 as T (s2, y, a2, b2)) =
      if Elem.leq (x, y) andalso size a1 >= size b1 + s2 then
        T (size a1 + size b1 + s2 + 1, x, a1, merge (b1, h2))
      else if Elem.leq (x, y) then
        T (size a1 + size b1 + s2 + 1, x, merge (b1, h2), a1)
      else if size a2 >= s1 + size b2 then
        T (size a2 + s1 + size b2 + 1, y, a2, merge (h1, b2))
      else
        T (size a2 + s1 + size b2 + 1, y, merge (h1, b2), a2)

  fun insert (x, E) = T (1, x, E, E)
    | insert (x, T (_, y, a, b)) =
      if Elem.leq (x, y) then
        makeT (x, a, insert (y, b))
      else
        makeT (y, a, insert (x, b))

  fun findMin E = raise EMPTY
    | findMin (T (_, x, _, _)) = x

  fun deleteMin E = raise EMPTY
    | deleteMin (T (_, _, a, b)) = merge (a, b)
end
