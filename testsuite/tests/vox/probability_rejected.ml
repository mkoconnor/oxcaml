(* TEST
 has-z3;
 flags = "-extension refinement_types";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml vox_probability.mli";
 prebuilt_modules += " vox_probability.ml";
 readonly_files = "probability_rejected.ml";
 { setup-ocamlc.opt-build-env; run-expect; check-program-output; }
 { flags = "-extension refinement_types -principal";
   setup-ocamlc.opt-build-env; run-expect; check-program-output; }
*)

#load "vox_sequence.cmo";;
#load "vox_real.cmo";;
#load "vox_real_credits.cmo";;
#load "vox_expectation.cmo";;
#load "vox_probability.cmo";;

module P = Vox_probability;;
module Q = Vox_real;;
module E = Vox_expectation;;
[%%expect{|
module P = Vox_probability
module Q = Vox_real
module E = Vox_expectation
|}]

let (draw @ total stateful) (bound : {n : int | 0 < n}) :
    {i : int | 0 <= i && i < bound} =
  let zeros = ghost_ (E.zeros (Bigint.of_int bound)) in
  ghost_ (E.zeros_facts (Bigint.of_int bound);
    E.zeros_mean (Bigint.of_int bound));
  let token = P.Cost.empty () in
  let #{P.index; cost = _} = P.uniform_cost bound zeros token in
  index;;
[%%expect{|
val draw : (bound : {n : int | 0 < n}) -> {i : int | (0 <= i) && (i < bound)} =
  <fun>
|}]

let erased () = ghost_ (draw 2);;
[%%expect{|
Line 1, characters 24-28:
1 | let erased () = ghost_ (draw 2);;
                            ^^^^
Error: The value "draw" is "stateful"
       but is expected to be "stateless"
         because it is used in an expression (at line 1, characters 16-31).
|}]

let (stateless @ total) () = draw 2;;
[%%expect{|
Line 1, characters 29-33:
1 | let (stateless @ total) () = draw 2;;
                                 ^^^^
Error: The value "draw" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at line 1, characters 24-35
         which is expected to be "stateless".
|}]

let (repeated @ total stateful) () : {n : int | n = 0} =
  let first = draw 2 in
  let second = draw 2 in
  first - second;;
[%%expect{|
Line 4, characters 2-16:
4 |   first - second;;
      ^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample)
Line 1, characters 48-53:
1 | let (repeated @ total stateful) () : {n : int | n = 0} =
                                                    ^^^^^
  The refinement is stated here.
|}]

let empty_range () = draw 0;;
[%%expect{|
Line 1, characters 26-27:
1 | let empty_range () = draw 0;;
                              ^
Error: Refinement could not be proved (counterexample)
Line 1, characters 48-53:
1 | let (draw @ total stateful) (bound : {n : int | 0 < n}) :
                                                    ^^^^^
  The refinement is stated here.
|}]

let convert (token : P.Cost.token @ unique total ghost) =
  (token : P.Error.token);;
[%%expect{|
Line 2, characters 3-8:
2 |   (token : P.Error.token);;
       ^^^^^
Error: The value "token" has type "P.Cost.token" = "Vox_probability.Cost.token"
       but an expression was expected of type
         "P.Error.token" = "Vox_probability.Error.token"
|}]

let mint () = P.Cost.Budget.create (Q.of_bigint 1Z);;
[%%expect{|
Line 1, characters 14-27:
1 | let mint () = P.Cost.Budget.create (Q.of_bigint 1Z);;
                  ^^^^^^^^^^^^^
Error: Unbound module "P.Cost.Budget"
|}]

let reset (monitor : P.monitor @ unique total ghost) =
  {monitor with seen = ghost_ false};;
[%%expect{|
Line 2, characters 16-20:
2 |   {monitor with seen = ghost_ false};;
                    ^^^^
Error: Unbound record field "seen"
|}]

let reuse (token : P.Cost.token @ unique total ghost) =
  let _ = P.Cost.split (ghost_ (Q.of_bigint 0Z)) token in
  P.Cost.split (ghost_ (Q.of_bigint 0Z)) token;;
[%%expect{|
Line 3, characters 41-46:
3 |   P.Cost.split (ghost_ (Q.of_bigint 0Z)) token;;
                                             ^^^^^
Error: This value is used here, but it has already been used as unique at:
Line 2, characters 49-54:
2 |   let _ = P.Cost.split (ghost_ (Q.of_bigint 0Z)) token in
                                                     ^^^^^

|}]

let unpaid_failure (monitor : {m : P.monitor | not (P.failed m)}
    @ unique total ghost) =
  let error = P.Error.empty () in
  P.checkpoint false monitor error;;
[%%expect{|
Line 4, characters 29-34:
4 |   P.checkpoint false monitor error;;
                                 ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_probability.mli", lines 19-20, characters 30-43:
  The refinement is stated here.
|}]

let underfunded (alloc : {qs : Q.t list |
    Vox_sequence.length qs = 2Z && Q.all_nonnegative qs &&
    E.uniform qs === Q.of_bigint 1Z} @ ghost) =
  let token = P.Cost.empty () in
  P.uniform_cost 2 alloc token;;
[%%expect{|
Line 5, characters 25-30:
5 |   P.uniform_cost 2 alloc token;;
                             ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_probability.mli", line 53, characters 28-67:
  The refinement is stated here.
|}]

let negative_allocation (alloc : {qs : Q.t list |
    Vox_sequence.length qs = 2Z && not (Q.all_nonnegative qs)} @ ghost) =
  let token = P.Cost.empty () in
  P.uniform_cost 2 alloc token;;
[%%expect{|
Line 4, characters 19-24:
4 |   P.uniform_cost 2 alloc token;;
                       ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_probability.mli", line 52, characters 4-24:
  The refinement is stated here.
|}]

let wrong_length () =
  let alloc = ghost_ (E.zeros 1Z) in
  ghost_ (E.zeros_facts 1Z);
  let token = P.Cost.empty () in
  P.uniform_cost 2 alloc token;;
[%%expect{|
Line 5, characters 19-24:
5 |   P.uniform_cost 2 alloc token;;
                       ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_probability.mli", line 51, characters 28-61:
  The refinement is stated here.
|}]

let unpaid_work_on_failure
    (_monitor : {m : P.monitor | P.failed m} @ unique total ghost) =
  let token = P.Cost.empty () in
  P.Cost.tick token;;
[%%expect{|
Line 4, characters 14-19:
4 |   P.Cost.tick token;;
                  ^^^^^
Error: Refinement could not be proved (counterexample)
File "vox_real_credits.mli", line 18, characters 35-68:
  The refinement is stated here.
|}]
