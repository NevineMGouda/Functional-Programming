(* Assignment 2 Group 5
 * Gouda, Nevine
 * Mellberg, Andreas
 *)


(* No function in any solution have side effects unless stated otherwise
   in the function specification. *)

(*******************************************************************************
 * Problem 1: Iota
 ******************************************************************************)

(* iota n
   TYPE: int -> int list
   PRE: true
   POST: [0, 1, ..., n-1]
   SIDE EFFECTS: Domain exception raised if n < 1
   EXAMPLES: iota 1 = [0]
             iota 5 = [0, 1, 2, 3, 4]
*)
fun iota n =
    if n <= 0 then []
    else
        let
            (* buildList (n, L)
               TYPE: int * int list -> int list
               PRE: n >= 0
               POST: [0, 1, ..., n] @ L
               EXAMPLES: buildList 4 = [0, 1, 2, 3, 4]
            *)
            (* VARIANT: n *)
            (* We use tail recursion to speed up the list construction *)
            fun buildList (0, L) = [0] @ L
              | buildList (n, L) = buildList (n-1, [n] @ L)
        in
            buildList (n-1, [])
        end


(*******************************************************************************
 * Problem 2: Intersection
 ******************************************************************************)

(* 1 *)

(* member x L
   TYPE: ''a -> ''a list -> bool
   PRE: true (note that x and the values in L must be of equality type)
   POST: true if L contains x, false if not
   EXAMPLES: member 2 [1,2,3] = true
             member 0 [] = false
             member "str" ["some","strings","str"] = true
*)
(* VARIANT: length of L *)
fun member a nil = false
  | member a (x::xs) =
        if a = x then
            true
        else
            member a xs

(* inter s1 s2
   TYPE: ''a list -> ''a list -> ''a list
   PRE: true
   POST: all elements contained in both s1 and s2 (i.e. their intersection)
   EXAMPLES: inter [] [1,2] = []
             inter [2,1,7,3] [3,6,2] = [2,3]
*)
(* VARIANT: length of s1 *)
(* Obviously it would be better to recurse into the shortest list, instead
   of the first argument as done here, but since the function is slow
   anyway we skip this check. inter' below is a much improved version. *)
fun inter nil _ = nil
  | inter (x::xs) s2 =
        if member x s2 then
            [x] @ inter xs s2
        else
            inter xs s2;

(* 2 *)

(* inter' s1 s2
   TYPE: int list -> int list -> int list
   PRE: both s1 and s2 are ordered
   POST: all elements contained in both s1 and s2 (i.e. their intersection)
   EXAMPLES: inter' [1] [1,2] = [1]
             inter' [1,3,5,7,9,11] [2,3,5,7,11,13] = [3,5,7,11]
*)
(* VARIANT: length of s1 + length of s2 *)
fun inter' nil _ = nil
  | inter' _ nil = nil
  | inter' (x::xs) (y::ys) =
        if x < y then
            inter' xs (y::ys)
        else if x > y then
            inter' (x::xs) ys
        else
            [x] @ inter' xs ys

(* 3 *)

(* Executing tests of inter and inter' on lists created by calls to iota we
   get the following measurements:
       inter s1 s2: 6.607
      inter' s1 s2: 0.012
   (These are typical results seen, where s1 contains 10^5 ordered elements
    and s2 contains 10^6 elements.) Clearly inter' is a huge improvement: it can
    disregard large parts of the lists in each recursive call by using the
    assumed order of the input lists. *)


(*******************************************************************************
 * Problem 3: Fruit
 ******************************************************************************)

(* 1 *)
(* REPRESENTATION CONVENTION: fruit represents three types of fruit: Apple:s,
                              Banana:s and Lemon:s. Apples and bananas have an
                              associated weight, while lemons are given in units
   REPRESENTATION INVARIANT: Apple is associated with a nonnegative real,
                             Banana with a nonnegative real,
                             Lemon with a nonnegative int
 *)
datatype fruit = Apple of real | Banana of real | Lemon of int;

(* 2 *)
(* sumPrice fruitList applePrice bananaPrice lemonPrice
   TYPE: fruit list -> real -> real -> real -> real
   PRE: applePrice, bananaPrice, lemonPrice are nonnegative reals
   POST: total cost of all items in the list
   EXAMPLES: sumPrice [] 1.0 1.0 1.0 = 0.0
             sumPrice [Apple 3.0] 1.0 2.0 3.0 = 3.0
             sumPrice [Apple 3.5, Banana 4.0, Lemon 5] 10.0 11.0 12.0 = 139.0
*)
fun sumPrice fruitList applePrice bananaPrice lemonPrice =
    let
        (* price fruit
           TYPE: fruit -> real
           PRE: the real value bindings applePrice, bananaPrice and lemonPrice
                have to be available
           POST: cost of fruit
           EXAMPLE: Assuming lemonPrice is 5.0:
                     price (Lemon 4) = 20.0
        *)
        fun price (Apple weight) = weight * applePrice
          | price (Banana weight) = weight * bananaPrice
          | price (Lemon units) = real(units) * lemonPrice;

        (* compute fruitList total
           TYPE: fruit list -> real -> real
           PRE: true
           POST: total cost of all items in the list
           EXAMPLES: compute [Apple 3.0] 0.0 = 3.0
                     compute [] 5.0 = 5.0
        *)
        (* VARIANT: length of fruitList *)
        (* We recurse through the list and compute each price and add it
           to a running total passed into each recursive call (achieving
           tail recursion). *)
        fun compute (nil, total) = total
          | compute (x::xs, total) = compute(xs, total + price x);
    in
        compute(fruitList, 0.0)
    end


(*******************************************************************************
 * Problem 4: Trees
 ******************************************************************************)

(* 1 *)

(* REPRESENTATION CONVENTION: Recursive data structure containing Node:s that
                              together represents a general tree. Each Node
                              is a pair where the first component is a label
                              and the second is a list of such Node:s
                              (the recursive part of the definition).
   REPRESENTATION INVARIANT: The first component of each Node is a value of
                             polymorphic type 'a, and the second is a list of
                             Node values. A tree consists of at least one Node.
 *)
datatype 'a ltree = Node of ('a * ('a ltree) list);

(* 2 *)

(* The idea for each of these functions is to reduce the problem size in
   each recursive call by separating the head (a Node) and creating a new
   temporary Node with the tail (a Node list) as children. *)

(* count tree
   TYPE: 'a ltree -> int
   PRE: true
   POST: number of nodes in tree
   EXAMPLES: count (Node("a", nil)) = 1
             count (Node(1, [
                        Node(2, [
                            Node(5,nil)
                        ]),
                        Node(3,nil),
                        Node(4, [
                            Node(6,nil),
                            Node(7,nil)
                        ])
                    ])) = 7
*)
(* VARIANT: length of list of Node:s in tree *)
fun count (Node (_, nil)) = 1
  | count (Node (label, x::xs)) = count x + count (Node (label, xs));

(* labels tree
   TYPE: 'a ltree -> 'a list
   PRE: true
   POST: list of all labels/values in tree
   EXAMPLES: labels (Node (1, [Node (2, [])])) = [2, 1]
*)
(* VARIANT: length of list of Node:s in tree *)
fun labels (Node (label, nil)) = [label]
  | labels (Node (label, x::xs)) = labels x @ labels (Node (label, xs));

(* is_present tree val
   TYPE: ''a ltree -> ''a -> bool
   PRE: the types of the labels in tree and the type of val have to be the same
   POST: true if val is contained in tree, false otherwise
   EXAMPLES: is_present (Node(3, [])) 3 = true
             is_present (Node(1, [
                             Node(2, [
                                 Node(5,nil)
                             ]),
                             Node(3,nil),
                             Node(4, [
                                 Node(6,nil),
                                 Node(7,nil)
                             ])
                         ])) 8 = false
*)
(* VARIANT: length of list of Node:s in tree *)
fun is_present (Node (label, nil)) value = (label = value)
  | is_present (Node (label, x::xs)) value =
        (is_present x value) orelse (is_present (Node (label, xs)) value);

(* height tree
   TYPE: 'a ltree -> int
   PRE: true
   POST: height of tree
   EXAMPLES: height (Node(3, [])) = 1
             height (Node(1, [
                         Node(2, [
                             Node(5,nil)
                         ]),
                         Node(3,nil),
                         Node(4, [
                             Node(6,nil),
                             Node(7,nil)
                         ])
                     ])) = 3
*)
(* VARIANT: length of list of Node:s in tree *)
fun height (Node (_, nil)) = 1
  | height (Node (label, x::xs)) =
        (* We must add 1 to the subtree formed by the head to account for
           the fact that the subtree corresponding to the tail is rooted
           one level above. *)
        Int.max (1 + height x, height (Node (label, xs)));


(* REFERENCE USED:
 * The course text by Ullman was helpful for getting started, specifically
 * the case study of general rooted trees in Section 6.4, pp. 223-226.
 * Ullman, Jeffrey D., "Elements of ML programming", 1998
 *)