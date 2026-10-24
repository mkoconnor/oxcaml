(* TEST
 has-z3;
 flags = "-extension refinement_types";
 { expect; }
*)

type t = Foo | Bar | Baz

(* The refinement excludes [Bar] and [Baz], so the match is exhaustive. *)
let f (x : {x : t | match x with Foo -> true | Bar | Baz -> false}) =
  match x with Foo -> 17;;
[%%expect{|
type t = Foo | Bar | Baz
val f : {x : t | match x with | Foo -> true | Bar | Baz -> false} -> int =
  <fun>
|}]

(* A case for a value the refinement excludes is rejected. *)
let g (x : {x : t | match x with Foo -> true | Bar | Baz -> false}) =
  match x with Foo -> 17 | Bar -> 18 | Baz -> 19;;
[%%expect{|
Line 2, characters 27-30:
2 |   match x with Foo -> 17 | Bar -> 18 | Baz -> 19;;
                               ^^^
Error: This match case is impossible: the refinements in scope exclude every value it matches.
       Hint: remove it, or make its body "unreachable_ ()".
|}]

(* Facts on the path count too. *)
let h (x : t) =
  match x with
  | Foo -> 0
  | Bar | Baz ->
    match x with Bar -> 1 | Baz -> 2;;
[%%expect{|
val h : t -> int = <fun>
|}]

let h_impossible (x : t) =
  match x with
  | Foo -> 0
  | Bar | Baz ->
    match x with Foo -> 1 | Bar -> 2 | Baz -> 3;;
[%%expect{|
val h_impossible : t -> int = <fun>
|}]

(* A match that remains non-exhaustive keeps its warning. *)
let partial (x : {x : t | match x with Baz -> false | Foo | Bar -> true}) =
  match x with Foo -> 17;;
[%%expect{|
Line 2, characters 2-24:
2 |   match x with Foo -> 17;;
      ^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
  Here is an example of a case that is not matched: "(Bar|Baz)"

val partial :
  {x : t | match x with | Baz -> false | Foo | Bar -> true} -> int = <fun>
|}]

(* A case written to be unreachable is accepted. *)
let marked (x : {x : t | match x with Foo -> true | Bar | Baz -> false}) =
  match x with
  | Foo -> 17
  | Bar -> unreachable_ ()
  | Baz -> assert false;;
[%%expect{|
val marked : {x : t | match x with | Foo -> true | Bar | Baz -> false} -> int =
  <fun>
|}]

(* Cases of a match on an unreachable path are not reported. *)
let dead (x : {x : t | match x with Foo -> true | Bar | Baz -> false})
    (n : {n : int | n > 0}) =
  if n < 0 then (match x with Foo -> 1 | Bar -> 2 | Baz -> 3) else 0;;
[%%expect{|
val dead :
  {x : t | match x with | Foo -> true | Bar | Baz -> false} ->
  {n : int | n > 0} -> int = <fun>
|}]

(* Integers. *)
let sign (n : {n : int | n >= 0}) =
  match n with 0 -> "zero" | n when n > 0 -> "positive";;
[%%expect{|
val sign : {n : int | n >= 0} -> string = <fun>
|}]

(* In total code the missing cases must be excluded. *)
let (total_f @ total) (x : {x : t | match x with Foo -> true | Bar | Baz -> false}) =
  match x with Foo -> 17;;
[%%expect{|
val total_f :
  {x : t | match x with | Foo -> true | Bar | Baz -> false} -> int = <fun>
|}]

let (total_partial @ total)
    (x : {x : t | match x with Baz -> false | Foo | Bar -> true}) =
  match x with Foo -> 17;;
[%%expect{|
Line 3, characters 2-24:
3 |   match x with Foo -> 17;;
      ^^^^^^^^^^^^^^^^^^^^^^
Error: This pattern-matching in total code is not exhaustive, and the refinements in scope do not exclude the missing cases.
       Here is an example of a case that is not matched:
         "(Bar|Baz)"
|}]

(* Without an annotation, a partial match still makes the function partial. *)
let inferred (x : {x : t | match x with Baz -> false | Foo | Bar -> true}) =
  match x with Foo -> 17;;
[%%expect{|
Line 2, characters 2-24:
2 |   match x with Foo -> 17;;
      ^^^^^^^^^^^^^^^^^^^^^^
Warning 8 [partial-match]: this pattern-matching is not exhaustive.
  Here is an example of a case that is not matched: "(Bar|Baz)"

val inferred :
  {x : t | match x with | Baz -> false | Foo | Bar -> true} -> int = <fun>
|}]

(* A proof omits the combinations its premise excludes. *)
type nat = Z | S of nat [@@inductive]

let[@def] rec (same_shape @ total) (a : nat) (b : nat) : bool =
  match a, b with
  | Z, Z -> true
  | S a, S b -> same_shape a b
  | _ -> false;;
[%%expect{|
type nat = Z | S of nat [@@inductive]
val same_shape : nat -> nat -> bool = <fun>
val same_shape_def :
  (a' : nat) ->
  (b' : nat) ->
  {u : unit
    | (same_shape a' b') ===
        (match (a', b') with
         | (Z, Z) -> true
         | (S a, S b) -> same_shape a b
         | _ -> false : bool)} =
  <fun>
|}]

let rec (same_shape_equal @ total) :
    (a : nat) -> (b : nat) ->
    {u : unit | if same_shape a b then a === b else true} = fun a b ->
  if same_shape a b then
    (same_shape_def a b;
     match a with
     | Z -> (match b with Z -> ())
     | S a' -> (match b with S b' -> same_shape_equal a' b'; ()))
  else ();;
[%%expect{|
val same_shape_equal :
  (a : nat) ->
  ((b : nat) -> {u : unit | if same_shape a b then a === b else true}) @ total
  stateful = <fun>
|}]

(* A case that earlier cases already cover is left to warning 11. *)
let covered (x : {x : t | match x with Foo -> true | Bar | Baz -> false}) =
  (match x with _ -> 0 | Foo -> 1) [@warning "-11"];;
[%%expect{|
val covered :
  {x : t | match x with | Foo -> true | Bar | Baz -> false} -> int = <fun>
|}]
