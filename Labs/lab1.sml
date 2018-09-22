(* Assignment 1
 * Group 26:
 * Andreas Mellberg
 * Nevine Gouda
 *)


(*******************************************************************************
 * Problem 1: Reduction, Specification and Variant
 *******************************************************************************

1.
product 3
-> 3 * product (3-1) -> 3 * product 2
-> 3 * (2 * product (2-1)) -> 3 * (2 * product 1)
-> 3 * (2 * 1) -> 3 * 2 -> 6

2.
It computes n! = n * (n-1) * ... * 1, i.e. the factorial of n.

3.
(* product n
   TYPE: int -> int
   PRE: n > 0
   POST: n! = n * (n-1) * ... * 1
   SIDE EFFECTS: none
   EXAMPLES: product 3 = 6
             product 5 = 120
*)

4.
(* VARIANT: n *)
*)


(*******************************************************************************
 * Problem 2: Currying
 ******************************************************************************)

(* 1. *)

(* Anonymous function with signature x y
   TYPE: int -> int -> int
   PRE: x and y any integers
   POST: x - y
   SIDE EFFECTS: none
   EXAMPLES: assuming it is bound to identifier 'minus':
             minus 3 1 = 2
             minus 0 ~5 = 5
*)
val minus = fn x => fn y => x - y;

(*2.
First the function minus is applied to the value 5, giving a function
int -> int that maps y to the value 5 - y; this function is then applied to
the value 4, returning 5 - 4, or 1. This value is then stored in foo.
*)

(* 3.
The function minus is applied to 5, returning the function fn y => 5 - y,
which is stored in bar (so bar is now a function value, of type int -> int).
*)

(* 4.
minus 5 4
-> (fn x => fn y => x - y) 5 4
-> (fn x => (fn y => x - y)) 5 4
-> (fn y => 5 - y) 4
-> 5 - 4 -> 1
*)


(*******************************************************************************
 * Problem 3: Types
 ******************************************************************************)

(* fun1 n
   TYPE: int -> int
   PRE: none (n can be any integer)
   POST: n (it's the identity mapping)
   EXAMPLES: fun1 3 = 3, fun1 ~4 = ~4
*)
fun fun1 x:int = x;

(* fun2 m n
   TYPE: int -> int -> int
   PRE: none
   POST: product of m and n
   EXAMPLES: fun2 3 4 = 12
*)
fun fun2 x y = x * y;

(* fun3 n
   TYPE: int -> int * int
   PRE: none
   POST: the tuple (1, n)
   EXAMPLES: fun3 0 = (1, 0), fun3 5 = (1, 5)
*)
fun fun3 (x:int) = (1,x);

(* fun4 (x,y)
   TYPE: int * int -> int
   PRE: none
   POST: product of the tuple elements x and y
   EXAMPLES: fun4 (0,500) = 0, fun4 (5,2) = 10
*)
fun fun4 (x,y) = x * y;

(* fun5 x y z
   TYPE: int -> real -> string -> string
   PRE: x any integer, y any real, z any string
   POST: string representation of the real product of x and y
         concatenated with z
   EXAMPLES: fun5 3 4.0 " five" = "12.0 five"
             fun5 9 1.0 "" = "9.0"
*)
fun fun5 x y z = Real.toString(real(x) * y) ^ z;

(* fun6 (x, (y, z, w))
   TYPE: int * (string * string * int) -> int * string
   PRE: x and w any integers, y and z any strings
   POST: (x, str), where str is the concatenation of y, z and a
         string representation of w
   EXAMPLES: fun6 (1, ("foo", "bar", 2)) = (1, "foobar2")
             fun6 (~5, ("", "", ~5)) = (~5, "~5")
*)
fun fun6 (x:int, (y, z, w)) = (x, y ^ z ^ Int.toString(w));

(* None of the above functions have side effects. *)


(*******************************************************************************
 * Problem 4: Divisibility
 ******************************************************************************)

(* lcm n
   TYPE: int -> int
   PRE: none
   POST: l.c.m. of {1,2,...,n}; i.e. the smallest positive integer that is
         evenly divisible by all integers in the range [1,n]
   SIDE EFFECTS: Domain exception raised if n < 1
   EXAMPLES: lcm 2 = 2, lcm 5 = 60, lcm 10 = 2520, lcm 20 = 232792560,
             lcm ~1 gives a Domain exception
*)
fun lcm 1 = 1
  | lcm n =
       if n <= 0 then
          raise Domain
       else
          let
             (* buildList n
                TYPE: int -> int list
                PRE: n >= 1
                POST: the list of integers [1,2,...,n]
                SIDE EFFECTS: none (n < 1 is not handled, in accordance w/ PRE)
                EXAMPLES: buildList 4 = [1,2,3,4]
             *)
             (* VARIANT: n *)
             fun buildList 1 = [1]
               | buildList n = buildList (n-1) @ [n];

             (* lcmPair a b
                TYPE: int -> int -> int
                PRE: a >= 1, b >= 1
                POST: the least common multiple of a and b
                SIDE EFFECTS: none
                EXAMPLES: lcmPair 1 2 = 2, lcmPair 3 8 = 24
             *)
             fun lcmPair a b =
                let
                   (* gcd a b
                      TYPE: int -> int -> int
                      PRE: a >= 0, b >= 0
                      POST: the greatest common divisor of a and b
                      SIDE EFFECTS: none
                      EXAMPLES: gcd 5 2 = 1, gcd 6 4 = 2
                   *)
                   (* VARIANT: remainder when first argument a is divided
                               by the second argument b *)
                   fun gcd a 0 = a   (* Euclidean algorithm *)
                     | gcd a b = gcd b (a mod b)
                in
                   (a * b) div (gcd a b)
                end

             (* lcmList xs
                TYPE: int list -> int
                PRE: xs contains positive integers
                POST: the l.c.m. of the given integers
                SIDE EFFECTS: none
                EXAMPLES: lcmList [1,2,3] = 6,
                          lcmList [2,8,1,5] = 40
             *)
             (* VARIANT: the length of xs *)
             fun lcmList [m,n] = lcmPair m n
               | lcmList (m::ms) = lcmPair m (lcmList ms)
          in
             lcmList (buildList n)
          end


(* A DISCLOSURE NOTE / REFERENCES
 * The above solution was developed after being inspired by the following post:
 * https://stackoverflow.com/a/147523
 * This can be detected in the definition of lcmList. The other parts of the
 * solution contain implementations of standard algorithms to compute the
 * gcd and lcm of two numbers. As usual, Wikipedia was helpful:
 * https://en.wikipedia.org/wiki/Euclidean_algorithm
 *)