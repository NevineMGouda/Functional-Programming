(*
 * Assignment 4
 * Nevine Gouda
 *)


(* No functions in any solution have side effects unless stated otherwise. *)

(*******************************************************************************
* Test Function
******************************************************************************)
(*Note: This test function is copied from the lab4_test.sml*)
(* test test_name test_function
   TYPE: string -> (unit -> bool) -> unit
   PRE: true
   POST: ()
   SIDE-EFFECTS: any side-effects of test_function () other than
     exceptions; prints whether the test test_name succeeded (i.e.,
     test_function () = true), failed, or an exception was raised
 *)

fun test test_name test_function =
    (
        if test_function () then
            print (" + SUCCESSFUL TEST, name: " ^ test_name ^ "\n")
        else
            print (" - FAILED TEST, name: " ^ test_name ^ "\n")
    )
    handle _ =>
        print (" - EXCEPTION RAISED IN TEST, name: " ^ test_name ^ "\n");

(*******************************************************************************
 * Problem 1: A Signature for valuations
 ******************************************************************************)
signature VALUATION =
  sig
    type T
    val empty: T
    val set: T -> string -> bool -> T
    val value_of: T -> string -> bool
    val variables: T -> string list
    val print: T -> unit
  end;

(*******************************************************************************
 * Problem 2: A Structure for valuations
 ******************************************************************************)
(*** 1. ***)

(*FIX*)
(* set_replace vl vs vb
   TYPE: T -> unit
   PRE: elements in vl should be a pair of (string, bool)
   POST: sets new pair in the list of valuations and if the variable exists it replaces it with new value
*)

(* set vl vs vb
   TYPE: T -> string -> bool -> T
   PRE: true
   POST: the list of valuations with the string and its boolean evaluation appended to the list
*)

(* value_of t vs
   TYPE: T -> string -> bool
   PRE: true
   POST: returns the boolean evaluation of t if it exists in the valuation
*)

(* variables t
   TYPE: T -> string list
   PRE: true
   POST: A list of variables in the valuation*)

(* print vl vs vb
   TYPE: T -> unit
   PRE: true
   POST: prints the strings with their corresponding valuations
*)

structure Valuation :> VALUATION =
  struct
    type T = (string * bool) list
    val empty = []

    fun set_replace [] vs vb = if vs = "found" then [] else [(vs, vb)]
      | set_replace ((x, y)::xs) vs vb =
        if vs = x then
     	    (vs,vb)  :: set_replace xs "found" vb
    	  else
    	    (x, y) :: set_replace xs vs vb

    fun set [] vs vb = (vs, vb) :: []
      | set vl vs vb = set_replace vl vs vb

    fun value_of [] x = false
      | value_of ((x, y)::xs) vs =
  	   if vs = x then
   	    y
  	   else
  	    value_of xs vs

    fun variables [] = []
      | variables ((x, y)::xs) =
  	     x::(variables xs)

    fun print valuation =
      (
        List.app(fn name =>
  					       TextIO.print (name ^ " = " ^ Bool.toString (value_of valuation name) ^ "\n")
                )
  				 (variables valuation);
  			TextIO.print "\n"
      )

  end;


(*** 2. ***)
(* set function’s complexity:
		It has a complexity of constant time, since the number of operations performed is bounded by a constant. *)

(* value_of function’s complexity:
		It has a linear time complexity. In other words the worst case complexity is = n, where n is the size of the list.
		And the worst case is that the element doesn’t exist.*)

(* variables function’s complexity:
		It has a fixed linear time complexity. In other words it always takes n times to finish. Where n I is the size of the list. *)

(*print function’s complexity:
		It has a fixed linear time complexity. In other words it always takes n times to finish. Where n I is the size of the list. *)

(*******************************************************************************
 * Problem 3: A Functor for Propositional Logic
 ******************************************************************************)
datatype formula = True
		| False
		| Var of string
		| Not of formula
		| And of formula * formula
		| Or of formula * formula;

(*signature SEMANTICS
sig
  val truth_value: V.T −> formula −> bool
  val is_taut: formula −> bool
end;*)

(* variables_list formula
   TYPE: formula -> string list
   PRE: true
   POST: returns all the variables mentioned in a formula, with duplicates
   EXAMPLE: variables_list (Not (And (And (False, Var "x"), Var "y"))) = ["x", "y"]
            variables_list (Not (And (And (False, Var "x"), Var "x"))) = ["x", "x"]
	    variables_list (Not(True)) = []
  	    variables_list (Not(Var "x")) = ["x"]

*)

fun variables_list (Var x) = [x]
  | variables_list (False) = []
  | variables_list (True) = []
  | variables_list (Not (f)) = variables_list (f)
  | variables_list (And (fx, fy)) = variables_list (fx) @ variables_list (fy)
  | variables_list (Or (fx, fy)) = variables_list (fx) @ variables_list (fy);

(* remove_dup l
   TYPE: ''a list -> ''a list
   PRE: true
   POST: returns the same list but with duplicates removed
   EXAMPLE: remove_dup [] = []
	    remove_dup ["x", "y"] = ["x", "y"]
	    remove_dup ["x", "x"] = ["x"]
	    remove_dup ["x"] = ["x"]

*)
fun remove_dup [] = []
  | remove_dup (x::xs) = x:: remove_dup(List.filter (fn y => y <> x) xs);

(* generate formula
   TYPE: a list -> ('a * bool) list list
   PRE: true
   POST: returns the truth table for a list of variables
   EXAMPLE: generate [] = [[]]
	    generate ["a"] = [[("a",true)],
			     [("a",false)]]
	    generate ["a", “b”] = [[("a",true),("b",true)],
				   [("a",true),("b",false)],
				   [("a",false),("b",true)],
				   [("a",false),("b",false)]]
*)

fun generate [] = [[]]
  | generate (x :: xs) =
    let
      val txs = generate xs
    in
      map (fn l => (x, true) :: l) txs @ map (fn l => (x, false) :: l) txs
    end;


(* truth_value v formula
   TYPE: V.T −> formula −> bool
   PRE: true
   POST: returns the truth value for a formula
   EXAMPLE: truth_value [(“y”, false)] (Not(Not(Not(Not(Not(Var "y")))))) = false
            truth_value [(“x”, true),(“y”, false)] (Or(And (Var "x", Var "x"), And (Var "y", Var "y"))) = true
*)
functor SEM(V: VALUATION) =
  struct
    fun truth_value v (Var x) = V.value_of v x
     | truth_value v (True) = true
     | truth_value v (False) = false
     | truth_value v (Not f) = not (truth_value v f)
     | truth_value v (And (fx, fy)) = (truth_value v (fx)) andalso (truth_value v (fy))
     | truth_value v (Or (fx, fy)) =  (truth_value v (fx)) orelse (truth_value v (fy));
  end;

structure tempSem = SEM(Valuation);

(* trial list formula
   TYPE: (string * bool) list -> formula -> bool
   PRE: true
   POST: returns the truth value for a formula given the variables trial's values
   EXAMPLE: trial [("x",true)] And(False, Var "x") = false
            trial [("x",true)] And(True, Var "x") = true
            trial [("x",true),("y",true)] And(Var "y", Var "x") = true
            trial [("x",false),("y",true)] And(Var "y", Var "x") = false
            trial [("x",false),("y",true)] Or(Var "y", Var "x") = true
*)

(* helper list formula
   TYPE: (string * bool) list list * formula -> bool
   PRE: true
   POST: returns if formula is taulogy or not where it is a tautology if all possible values for variables return true
   EXAMPLE: helper [[("x",true)],[("x",false)]] And(False, Var "x") = false
            helper [[("x",true)],[("x",false)]] And(True, Var "x") = false
            helper [[("x",true)],[("x",false)]] Or(True, Var "x") = true
            helper [[("x",true),("y",true)],[("x",false),("y",true)],
                    [("x",true),("y",false)],[("x",false),("y",false)]] And(Var "y", Var "x") = false
*)

(* truth_value v formula
   TYPE: V.T −> formula −> bool
   PRE: true
   POST: returns the truth value for a formula
   EXAMPLE: truth_value [(“y”, false)] (Not(Not(Not(Not(Not(Var "y")))))) = false
            truth_value [(“x”, true),(“y”, false)] (Or(And (Var "x", Var "x"), And (Var "y", Var "y"))) = true
*)

(* is_taut formula
   TYPE: formula −> bool
   PRE: true
   POST: returns the truth value for a formula
   EXAMPLE: is_taut (Var “x”) = false
            is_taut (Var "x", Not (Var "x")) = true
*)

functor Semantics(V: VALUATION) =
  struct
    fun truth_value v (Var x) = V.value_of v x
     | truth_value v (True) = true
     | truth_value v (False) = false
     | truth_value v (Not f) = not (truth_value v f)
     | truth_value v (And (fx, fy)) = (truth_value v (fx)) andalso (truth_value v (fy))
     | truth_value v (Or (fx, fy)) =  (truth_value v (fx)) orelse (truth_value v (fy));

    fun trial x f =
      let
        val v = foldl (fn ((name,value), v) => Valuation.set v name value)
                Valuation.empty
                x
      in
        tempSem.truth_value v f
      end;

    fun helper ([],f) = true
      | helper ((x::xs),f) =
          if trial x f = true then
             helper (xs,f)
          else
             false;

    fun is_taut f = helper(generate(remove_dup(variables_list(f))),f);

  end;

(* 2. *)
structure Seman = Semantics(Valuation);
val v = foldl (fn ((name,value), v) => Valuation.set v name value)
    Valuation.empty
    [("x",true), ("y",false)];

(* Test N *)
  test "N_1"
      (fn () => not (Seman.truth_value v (Var "y")));
  test "N_2"
      (fn () => Seman.truth_value v (Var "x"));
  test "N_3"
      (fn () => Seman.truth_value v (Not(Var "y")));
  test "N_4"
      (fn () => Seman.truth_value v (Not(Not(Not(Not(Not(Var "y")))))));
  test "N_5"
      (fn () => Seman.truth_value v (And (Var "x", True)));
  test "N_6"
      (fn () => not(Seman.truth_value v (And(And (True, True), And (False, False))) ));
  test "N_7"
      (fn () => Seman.truth_value v (Or(And (Var "x", Var "x"), And (Var "y", Var "y"))));

(* Test M *)
  test "M_1"
      (fn () => not (Seman.is_taut (Var "y") ));
  test "M_2"
      (fn () => not (Seman.is_taut (Not(Var "y")) ));
  test "M_3"
      (fn () => Seman.is_taut True);
  test "M_4"
      (fn () => not(Seman.is_taut (Not(Not(Not(Not(Not(Var "y")))))) ));
  test "M_5"
      (fn () => not(Seman.is_taut (And (Var "x", True)) ));
  test "M_6"
      (fn () => Seman.is_taut (Or (Var "x", True)) );
  test "M_7"
      (fn () => not(Seman.is_taut (And(And (True, True), And (True, False))) ));
  test "M_8"
      (fn () => Seman.is_taut (Or(And (True, True), And (True, False))) );
  test "M_9"
      (fn () => Seman.truth_value v (Or(And (Var "x", Var "x"), Or (True, Var "y"))));



(*******************************************************************************
 * Problem 4: Simplification of Propositional Formulas
 ******************************************************************************)
(*1. *)
(* simp formula
   TYPE: formula −> formula
   PRE: true
   POST: tries to simplify the formula
   EXAMPLE: simp (Not (And (And (True, Var "x"), False))) = True
            simp (Not(Not(True)) = True
            simp (Not(False)) = True
	          simp (And (False, Var "x")) = False
*)

fun simp (Var x) = Var x
  | simp True = True
  | simp False = False
  | simp (Not(True)) = False
  | simp (Not(False)) = True
  | simp (Not(Not x)) = simp x
  | simp (Not(Var x)) = (Not(Var x))
  | simp (Not(x)) = simp (Not(simp x))
  | simp (And(True, x)) = simp x
  | simp (And(x, True)) = simp x
  | simp (And(False, x)) = False
  | simp (And(x, False)) = False
  | simp (And(Var x, Var y)) = (And(Var x, Var y))
  | simp (And(x, Var y)) = (And(simp x, Var y))
  | simp (And(Var x, y)) = (And(Var x, simp y))
  | simp (And(x, y)) = (And(simp x, simp y))
  | simp (Or(x, True)) = True
  | simp (Or(False, x)) = simp x
  | simp (Or(x, False)) = simp x
  | simp (Or(True, x)) = True
  | simp (Or (Var x, Var y)) = (Or(Var x, Var y))
  | simp (Or (x, Var y)) = (Or(simp x, Var y))
  | simp (Or (Var x, y)) = (Or(Var x, simp y))
  | simp (Or (x, y)) = simp (Or(simp x, simp y));

(*2. *)

(* Test T *)
 test "T_1"
 	(fn () => simp (Not (Not(Var "a"))) = Var "a");

 test "T_2"
        (fn () => simp (And (Not (Or (True, Var "x")), False)) = False);

 test "T_3"
 	(fn () => simp (False) = False);

 test "T_4"
 	(fn () => simp (Not (Not(True))) = True);

 test "T_5"
	(fn () => simp (Not (And (And (True, Var "x"), False))) = True);

  test "T_6"
 	(fn () => simp (Var "x") = Var "x");

  test "T_7"
 	(fn () => simp (Not (Var "x")) = Not (Var "x"));

(*******************************************************************************
 * End of Assignment
 ******************************************************************************)
