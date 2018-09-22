(*
 * Assignment 3
 * Andreas Mellberg (Group 25)
 * Nevine Gouda
 *)


(* No functions in any solution have side effects unless stated otherwise. *)


(*******************************************************************************
 * Problem 1: Tail Recursion
 ******************************************************************************)

fun average numbers =
    let
        fun compute nil avg _ = avg
          | compute (x::xs) avg len =
                compute xs ((x + real(len) * avg) / real(len + 1)) (len + 1)
    in
        compute numbers 0.0 0
    end

(* The function compute uses a standard formula for computing the cumulative
   moving average of the numbers in the list. See for example:
   https://en.wikipedia.org/wiki/Moving_average#Cumulative_moving_average
 *)


(*******************************************************************************
 * Problem 2: Specification
 ******************************************************************************)

(* average nums
   TYPE: real list -> real
   PRE: true
   POST: the average of the numbers in nums
   EXAMPLES: average [] = 0.0
             average [~1.0, 4.0, 6.0] = 3.0
*)

(* compute xs avg len
   TYPE: real list -> real -> int -> real
   PRE: len is nonnegative
   POST: the average of the numbers in xs
   EXAMPLES: compute [~1.0, 4.0, 6.0] 0.0 0 = 3.0
*)
(* VARIANT: length of xs *)


(*******************************************************************************
 * Problem 3: Use Of Higher-Order Functions
 ******************************************************************************)

(* 1 *)
(* append xs ys
   TYPE: 'a list -> 'a list -> 'a list
   PRE: true
   POST: xs concatenated with ys
   EXAMPLES: append [1,2,3] [4,5,6] = [1,2,3,4,5,6]
*)
(* Looking at the type of foldr, ('a * 'b -> 'b) -> 'b -> 'a list -> 'b,
   and the required type of append, 'a list -> 'a list -> 'a list (especially
   the range), we see that op:: is a perfect match (since it is of type
   'a * 'a list -> 'a list). Thus we can simply write: *)
fun append xs ys = foldr op:: ys xs;

(* The following also works -- it is simply being more explicit about the
   binary operation:
   fun append xs ys = foldr (fn (x,acc) => x::acc) ys xs; *)


(* 2 *)
(* member a xs
   TYPE: ''a -> ''a list -> bool
   PRE: true
   POST: true if and only if the value of a is contained in xs
   EXAMPLES: member "str" [] = false
             member 3 [1,3,5,7] = true
*)
fun member a xs = foldr (fn (x,acc) => acc orelse x = a) false xs;


(* 3 *)
(* last xs
   TYPE: 'a list -> 'a
   PRE: true
   POST: last element of xs
   SIDE-EFFECTS: EmptyList exception raised if xs is empty
   EXAMPLES: last [#"z"] = #"z"
             last [[1,2],[3,4],[5,6]] = [5,6]
*)
exception EmptyList;
fun last nil = raise EmptyList
  | last (x::xs) = foldl (fn (a,_) => a) x xs;


(* 4 *)
(* reverse xs
   TYPE: 'a list -> 'a list
   PRE: true
   POST: xs reversed
   EXAMPLES: reverse [1,2,3] = [3,2,1]
*)
fun reverse xs = foldl op:: [] xs;

(* Note: a function like the following, using foldr, is MUCH slower,
   I assume because of the linear complexity of the @ operator:
       fun reverse xs = foldr (fn (y,acc) => acc @ [y]) [] xs; *)


(* 5 *)
(* filter P xs
   TYPE: ('a -> bool) -> 'a list -> 'a list
   PRE: true
   POST: a list of all elements a in xs such that P a = true
   EXAMPLES: filter (fn x => x > 5) [3,14,11,4,8] = [14,11,8]
             filter (fn x => x mod 2 = 0) [2,3,5,7,11] = [2]
*)
fun filter P xs = foldr (fn (x,acc) => if P x then x::acc else acc) [] xs;


(*******************************************************************************
 * Problem 4: Binary Search Trees
 ******************************************************************************)

(* REPRESENTATION CONVENTION: A binary search tree that is either empty (Void)
    or consists of a Node represented by a left subtree, an integer value (the
    root value) and a right subtree (all packaged in a triple).
   REPRESENTATION INVARIANT: For any tree T, the root value of its left subtree
    (right subtree) is strictly smaller (larger) than the root value of T.
 *)
datatype tree = Void | Node of tree * int * tree;

(* fold_tree f y t
   TYPE: ('a * int * 'a -> 'a) -> 'a -> tree -> 'a
   PRE: true
   POST: f composed and evaluated over all levels of the tree t, with
         starting values f (y, k, y) for some int k at the leaf nodes.
         See also the answer to Problem 5.
   EXAMPLES:
     A function for checking if a tree contains some value a:
         fun member_tree a tree =
             fold_tree (fn (l,k,r) => (l orelse r) orelse k = a) false tree;
     To get a function computing tree height:
         fold_tree (fn (l,k,r) => 1 + Int.max(l,r)) 0
*)
(* VARIANT: The height of t. Since we step downwards to a child in each
    recursive call, obviously the height (a nonnegative integer) of the
    input tree decreases strictly. Hence each recursive path will reach
    the base case. *)
fun fold_tree f y Void = y
  | fold_tree f y (Node (l, k, r)) =
        f (fold_tree f y l, k, fold_tree f y r);

(* A small (and almost unnecessary) note:
   The definition of fold_tree as well as one of the examples in the
   specification is almost identical to the definition of fold functions for
   binary trees given in the lecture notes to this course. I assume that we
   are allowed to be inspired by and use this material freely in our
   solutions. *)

(* sub_tree a b t
   TYPE: int -> int -> tree -> tree
   PRE: true
   POST: a tree containing all keys from t that are >= a but < b
   EXAMPLES: sub_tree 3 6 Void = Void
             sub_tree 2 6 (Node (Node (Node (Void, 0, Node (Void, 2, Void)),
                                       3,
                                       Node (Void, 5, Void)),
                                 6,
                                 Node (Void,
                                       7,
                                       Node (Void, 8, Node (Void, 9, Void)))))
                 = Node (Node (Void, 2, Void), 3, Node (Void, 5, Void))
             sub_tree 6 2 (same tree as above) = Void
             sub_tree 6 6 (same tree as above) = Void
*)
fun sub_tree a b tree =
    let
        (* in_range a b k
           TYPE: int -> bool
           PRE: true
           POST: true if and only if k is in the integer range [a,b)
           EXAMPLES: in_range 0 0 0 = false
                     in_range 5 8 5 = true
        *)
        fun in_range a b k = a <= k andalso k < b;

        (* f (l, k, r)
           TYPE: (tree * int * tree) -> tree
           PRE: a function in_range as specified above must be defined in
                the current environment, as well as int bindings a and b
           POST: The tree having left (right) subtree l (r) if it is not
                 equal to Void, and root value k if it lies in [a,b);
                 if k is not in range the tree will be either l or r.
                 If l and r are both Void then the tree will be a leaf,
                 i.e. Node (Void, k, Void) if k is in range, Void if not.
           EXAMPLES: Assuming that a = 2 and b = 6:
                 f (Void, 8, Void) = Void
                 f (Node (Void, 2, Void), 4, Node (Void, 6, Void)) =
                     Node (Node (Void, 2, Void), 4, Node (Void, 6, Void))
                 f (Node (Void, 2, Void), 4, Void) =
                     Node (Node (Void, 2, Void), 4, Void)
                 f (Node (Void, 2, Void), 8, Void) = Node (Void, 2, Void)
        *)
        fun f (l, k, r) =
            (* Look at left and right trees and see if they contain something
               from the recursion, i.e. if they carry some Node that has a
               value in the range [a,b). *)
            if l <> Void then
                if r <> Void then
                    (* If both subtrees contain values in [a,b), then k is
                       also in [a,b) since we're in a binary search tree. *)
                    Node (l, k, r)
                else if in_range a b k then
                    Node (l, k, Void)
                else
                    l
            else if r <> Void then
                if in_range a b k then
                    Node (Void, k, r)
                else
                    r
            else if in_range a b k then
                Node (Void, k, Void)
            else
                Void;
    in
        fold_tree f Void tree
    end


(*******************************************************************************
 * Problem 5: Complexity
 *******************************************************************************

Obviously the time complexity of sub_tree as defined above is the same as the
complexity of fold_tree applied with the function f local to sub_tree. Looking
at fold_tree, we see that the recursive function calls will traverse down into
the tree until leaf nodes are hit, and during the recursive unwind (or unwinds,
rather) begin to evaluate f over the nodes. Intuitively one could visualize the
"fully expanded" expression of fold_tree, after all recursive paths have hit
bottom but before anything has been evaluated, as expressions nested in the
first and third arguments of f of the form
    f (f (f (..., k4, ...), k2, f (..., k5, ...)), k1, f (f (..., k6, ...), k3, f (..., k7, ...))).
Of course the nesting is finite, and at the "bottom layers" (corresponding to
leafs) we have expressions of the form f (y, k, y), where y is the starting
value given to fold_tree. We see that the running time of fold_tree is precisely
the time it takes to apply f to each node in the tree. Assuming that e.g. branch
checks and creating new Node:s take constant time (including executing
in_range), we see that each invocation of our f runs in constant time. Therefore
the complexity of fold_tree with this f must be bounded by some constant times
the number of nodes in the tree. Thus the (worst-case) time complexity of
sub_tree is linear with respect to the input size. *)
