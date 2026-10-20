(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml vox_real.mli";
 prebuilt_modules += " vox_real.ml vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml";
 readonly_files = "real_rejected.ml";
 {
   setup-ocamlc.opt-build-env;
   run-expect;
   check-program-output;
 }
*)

let zero_denominator () : Vox_real.t @ ghost =
  ghost_ (Vox_real.of_fraction 1Z 0Z);;
[%%expect{||}, Principal{|
Line 2, characters 34-36:
2 |   ghost_ (Vox_real.of_fraction 1Z 0Z);;
                                      ^^
Error: Refinement could not be proved (counterexample)
File "vox_real.mli", line 17, characters 32-38:
  The refinement is stated here.
|}]

let divide_by_zero (x : Vox_real.t) : Vox_real.t @ ghost =
  ghost_ (Vox_real.div x (Vox_real.of_bigint 0Z));;
[%%expect{||}, Principal{|
Line 2, characters 25-48:
2 |   ghost_ (Vox_real.div x (Vox_real.of_bigint 0Z));;
                             ^^^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_real.mli", line 12, characters 29-53:
  The refinement is stated here.
|}]

let symbolic_denominator (x : Vox_real.t) (y : Vox_real.t) =
  ghost_ (Vox_real.div x y);;
[%%expect{||}, Principal{|
Line 2, characters 25-26:
2 |   ghost_ (Vox_real.div x y);;
                             ^
Error: Refinement could not be proved (counterexample: y = 0)
File "vox_real.mli", line 12, characters 29-53:
  The refinement is stated here.
|}]

let cancelled_denominator (x : Vox_real.t) =
  ghost_ (Vox_real.div x (Vox_real.sub x x));;
[%%expect{||}, Principal{|
Line 2, characters 25-43:
2 |   ghost_ (Vox_real.div x (Vox_real.sub x x));;
                             ^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: x = 0)
File "vox_real.mli", line 12, characters 29-53:
  The refinement is stated here.
|}]

let negative_fraction_denominator () : Vox_real.t @ ghost =
  ghost_ (Vox_real.of_fraction 1Z (Bigint.neg 2Z));;
[%%expect{||}, Principal{|
Line 2, characters 34-49:
2 |   ghost_ (Vox_real.of_fraction 1Z (Bigint.neg 2Z));;
                                      ^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_real.mli", line 17, characters 32-38:
  The refinement is stated here.
|}]

let (unequal @ total) () : unit @ ghost = ghost_ (
  let half = Vox_real.of_fraction 1Z 2Z in
  let third = Vox_real.of_fraction 1Z 3Z in
  (() : {u : unit | half === third}));;
[%%expect{||}, Principal{|
Line 4, characters 3-5:
4 |   (() : {u : unit | half === third}));;
       ^^
Error: Refinement could not be proved (counterexample)
Line 4, characters 20-34:
4 |   (() : {u : unit | half === third}));;
                        ^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

let (integers_only @ total)
    (x : {q : Vox_real.t | Vox_real.lt (Vox_real.of_bigint 0Z) q &&
      Vox_real.lt q (Vox_real.of_bigint 1Z)}) :
    {u : unit | false} @ ghost = ghost_ ();;
[%%expect{||}, Principal{|
Line 4, characters 40-42:
4 |     {u : unit | false} @ ghost = ghost_ ();;
                                            ^^
Error: Refinement could not be proved (counterexample: x = 3/4)
Line 4, characters 16-21:
4 |     {u : unit | false} @ ghost = ghost_ ();;
                    ^^^^^
  The refinement is stated here.
|}]

let (underfunded_sample @ total) () : unit @ ghost = ghost_ (
  let zero = Vox_real.of_bigint 0Z in
  let one = Vox_real.of_bigint 1Z in
  let four = Vox_real.of_bigint 4Z in
  let branches = [zero; four] in
  Vox_sequence.length_def branches;
  Vox_sequence.length_def [four];
  Vox_sequence.length_def [];
  Vox_real.sum_def branches;
  Vox_real.sum_def [four];
  Vox_real.sum_def [];
  Vox_expectation.uniform_def branches;
  (() : {u : unit | Vox_real.le (Vox_expectation.uniform branches) one}));;
[%%expect{||}, Principal{|
Line 13, characters 3-5:
13 |   (() : {u : unit | Vox_real.le (Vox_expectation.uniform branches) one}));;
        ^^
Error: Refinement could not be proved (counterexample)
Line 13, characters 20-70:
13 |   (() : {u : unit | Vox_real.le (Vox_expectation.uniform branches) one}));;
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

module Reuse = struct
  module C = Vox_real_credits.Make ()
  let bad (token : {t : C.token |
      Vox_real.le (Vox_real.of_bigint 2Z) (C.credits t)}
      @ unique total ghost) =
    let _ = C.tick token in
    C.tick token
end;;
[%%expect{||}, Principal{|
Line 7, characters 11-16:
7 |     C.tick token
               ^^^^^
Error: This value is used here, but it has already been used as unique at:
Line 6, characters 19-24:
6 |     let _ = C.tick token in
                       ^^^^^

|}]

module Fractional_tick = struct
  module Q = Vox_real
  module C = Vox_real_credits.Make ()
  let bad () = ghost_ (
    let token = C.Budget.create (Q.of_fraction 1Z 2Z) in
    C.tick token)
end;;
[%%expect{||}, Principal{|
Line 6, characters 11-16:
6 |     C.tick token)
               ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_real_credits.mli", line 18, characters 35-68:
  The refinement is stated here.
|}]

module Mint (C : Vox_real_credits.S) = struct
  let bad () = C.Budget.create (Vox_real.of_bigint 1Z)
end;;
[%%expect{||}, Principal{|
Line 2, characters 15-23:
2 |   let bad () = C.Budget.create (Vox_real.of_bigint 1Z)
                   ^^^^^^^^
Error: Unbound module "C.Budget"
|}]

let runtime_value () : Vox_real.t @ real =
  Vox_real.of_fraction 1Z 2Z;;
[%%expect{||}, Principal{|
Line 2, characters 2-28:
2 |   Vox_real.of_fraction 1Z 2Z;;
      ^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This value is "ghost" but is expected to be "real".
|}]

let runtime_branch () : bool @ real =
  Vox_real.lt (Vox_real.of_bigint 0Z) (Vox_real.of_fraction 1Z 2Z);;
[%%expect{||}, Principal{|
Line 2, characters 14-37:
2 |   Vox_real.lt (Vox_real.of_bigint 0Z) (Vox_real.of_fraction 1Z 2Z);;
                  ^^^^^^^^^^^^^^^^^^^^^^^
Error: This value is "ghost" but is expected to be "real".
Hint: if this is proof code, wrap the enclosing expression in "ghost_ (...)".
|}]

let rec (halve @ total)
    (x : {q : Vox_real.t | Vox_real.lt (Vox_real.of_bigint 0Z) q}) :
    unit @ ghost = ghost_ (halve (Vox_real.divide x 2Z))
[@@decreases x];;
[%%expect{||}, Principal{|
Line 4, characters 13-14:
4 | [@@decreases x];;
                 ^
Error: The value "x" has type "Vox_real.t" but an expression was expected of type
         "int"
|}]

external forged_add : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
  @@ total = "caml_vox_real_add"

let forged (x : Vox_real.t) (y : Vox_real.t) :
    {q : Vox_real.t | q === Vox_real.add x y} @ ghost =
  ghost_ (forged_add x y);;
[%%expect{||}, Principal{|
Lines 1-2, characters 0-32:
1 | external forged_add : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
2 |   @@ total = "caml_vox_real_add"
Warning 228 [trusted-external]: The verifier assumes this external's totality;
  nothing checks it.

external forged_add : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
  = "caml_vox_real_add"
Line 6, characters 9-25:
6 |   ghost_ (forged_add x y);;
             ^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: x = 7719, y = 0)
Line 5, characters 22-44:
5 |     {q : Vox_real.t | q === Vox_real.add x y} @ ghost =
                          ^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

external forged_subtract : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
  @@ total = "caml_vox_real_add" "caml_vox_real_sub"

let different_native (x : Vox_real.t) (y : Vox_real.t) :
    {q : Vox_real.t | q === Vox_real.add x y} @ ghost =
  ghost_ (forged_subtract x y);;
[%%expect{||}, Principal{|
Lines 1-2, characters 0-52:
1 | external forged_subtract : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
2 |   @@ total = "caml_vox_real_add" "caml_vox_real_sub"
Warning 228 [trusted-external]: The verifier assumes this external's totality;
  nothing checks it.

external forged_subtract : Vox_real.t -> Vox_real.t -> Vox_real.t @ ghost
  = "caml_vox_real_add" "caml_vox_real_sub"
Line 6, characters 9-30:
6 |   ghost_ (forged_subtract x y);;
             ^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: x = 7719, y = 0)
Line 5, characters 22-44:
5 |     {q : Vox_real.t | q === Vox_real.add x y} @ ghost =
                          ^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

module Shadow = struct
  module Vox_real = struct
    type t = Bigint.t
    let[@def transparent] (of_fraction @ total) n d = Bigint.div n d
    let[@def transparent] (add @ total) (x : t) (y : t) = Bigint.add x y
  end
  let (fractional @ total) () : unit @ ghost = ghost_ (
    let half = Vox_real.of_fraction 1Z 2Z in
    (() : {u : unit | Vox_real.add half half = 1Z}))
end;;
[%%expect{||}, Principal{|
Line 9, characters 5-7:
9 |     (() : {u : unit | Vox_real.add half half = 1Z}))
         ^^
Error: Refinement could not be proved (counterexample)
Line 9, characters 22-49:
9 |     (() : {u : unit | Vox_real.add half half = 1Z}))
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

#load "vox_real.cmo";;
[%%expect{||}, Principal{|
|}]

module Sealed_zero : module type of Vox_real = Vox_real
let sealed_division_by_zero (x : Sealed_zero.t) =
  ghost_ (Sealed_zero.div x (Sealed_zero.of_bigint 0Z));;
[%%expect{||}, Principal{|
module Sealed_zero :
  sig
    type t : logical_data
    external of_bigint : Bigint.t -> t @ ghost @@ total
      = "caml_vox_real_of_bigint"
    external neg : t -> t @ ghost @@ total = "caml_vox_real_neg"
    external add : t -> t -> t @ ghost @@ total = "caml_vox_real_add"
    external sub : t -> t -> t @ ghost @@ total = "caml_vox_real_sub"
    external mul : t -> t -> t @ ghost @@ total = "caml_vox_real_mul"
    external div :
      t -> {y : t | not (y === (of_bigint (Bigint.of_int 0)))} -> t @ ghost
      @@ total = "caml_vox_real_div"
    external le : t -> t -> bool @ ghost @@ total = "caml_vox_real_le"
    external lt : t -> t -> bool @ ghost @@ total = "caml_vox_real_lt"
    type positive = {n : Bigint.t | n > (Bigint.of_int 0)}
    val of_positive :
      positive -> {q : t | not (q === (of_bigint (Bigint.of_int 0)))} @ ghost
      @@ total
    val of_positive_def :
      (n : positive) -> {u : unit | (of_positive n) === (of_bigint n)} @@
      total
    val of_fraction : Bigint.t -> positive -> t @ ghost @@ total
    val of_fraction_def :
      (n : Bigint.t) ->
      (d : positive) ->
      {u : unit | (of_fraction n d) === (div (of_bigint n) (of_positive d))}
      @@ total
    val divide : t -> positive -> t @ ghost @@ total
    val divide_def :
      (x : t) ->
      (n : positive) -> {u : unit | (divide x n) === (div x (of_positive n))}
      @@ total
    val nonnegative : t -> bool @ ghost @@ total
    val nonnegative_def :
      (x : t) ->
      {u : unit | (nonnegative x) === (le (of_bigint (Bigint.of_int 0)) x)}
      @@ total
    val sum : t list -> t @ ghost @@ total
    val sum_def :
      (values : t list) ->
      {u : unit
        | (sum values) ===
            (match values with
             | [] -> of_bigint (Bigint.of_int 0)
             | head::tail -> add head (sum tail))}
      @@ total
    val all_nonnegative : t list -> bool @ ghost @@ total
    val all_nonnegative_def :
      (values : t list) ->
      {u : unit
        | (all_nonnegative values) =
            (match values with
             | [] -> true
             | head::tail -> (nonnegative head) && (all_nonnegative tail))}
      @@ total
    val sum_nonnegative :
      (values : t list) ->
      {u : unit
        | if all_nonnegative values then nonnegative (sum values) else true} @ ghost
      @@ total
  end
Line 3, characters 28-54:
3 |   ghost_ (Sealed_zero.div x (Sealed_zero.of_bigint 0Z));;
                                ^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_real.mli", line 12, characters 29-53:
  The refinement is stated here.
|}]

let runtime_scalar_comparison
    (x : Vox_real.t @ ghost) (y : Vox_real.t @ ghost) : bool @ real =
  x < y;;
[%%expect{||}, Principal{|
Line 3, characters 2-3:
3 |   x < y;;
      ^
Error: This value is "ghost" but is expected to be "real".
Hint: if this is proof code, wrap the enclosing expression in "ghost_ (...)".
|}]
