(* TEST
 flambda2;
 flags = "-extension layouts";
 expect;
*)

(* Anonymous types of kind void, written [ `tag ]#, inhabited by #`tag.
   These generalise [unit#] (inhabited by [#()]): each is a distinct void
   type carrying no runtime information. *)

let x : [ `foo ]# = #`foo
let id (v : [ `foo ]#) : [ `foo ]# = v
[%%expect{|
val x : [ `foo ]# = <abstr>
val id : [ `foo ]# -> [ `foo ]# = <fun>
|}]

(* Different tags are different types. *)
let a : [ `bar ]# = #`bar
[%%expect{|
val a : [ `bar ]# = <abstr>
|}]

(* [#`foo] does not inhabit [ `bar ]#. *)
let bad : [ `bar ]# = #`foo
[%%expect{|
Line 1, characters 22-27:
1 | let bad : [ `bar ]# = #`foo
                          ^^^^^
Error: This expression has type "[ `foo ]#"
       but an expression was expected of type "[ `bar ]#"
|}]

(* The unboxed void type is distinct from the boxed polymorphic variant. *)
let bad (v : [ `foo ]#) : [ `foo ] = v
[%%expect{|
Line 1, characters 37-38:
1 | let bad (v : [ `foo ]#) : [ `foo ] = v
                                         ^
Error: The value "v" has type "[ `foo ]#" but an expression was expected of type
         "[ `foo ]"
|}]

(* The sole inhabitant can be matched on. *)
let use (v : [ `foo ]#) : int =
  match v with
  | #`foo -> 42
[%%expect{|
val use : [ `foo ]# -> int = <fun>
|}]

(* Being void, it occupies no space inside an unboxed product. *)
let pair : #(int * [ `foo ]#) = #(7, #`foo)
[%%expect{|
val pair : #(int * [ `foo ]#) = #(7, <abstr>)
|}]
