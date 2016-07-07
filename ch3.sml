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
