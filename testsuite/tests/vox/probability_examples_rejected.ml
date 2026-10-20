(* TEST
 has-z3;
 flags = "-extension refinement_types ";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_int_sequence.mli vox_int_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_quicksort_partition.ml";
 prebuilt_modules += " vox_sort_cost.mli vox_sort_cost.ml";
 prebuilt_modules += " vox_expectation.ml vox_harmonic.ml";
 prebuilt_modules += " vox_quicksort_cost.ml vox_quicksort_average.ml";
 prebuilt_modules += " vox_probability.mli vox_probability.ml";
 prebuilt_modules += " vox_randomized_quicksort.mli";
 prebuilt_modules += " vox_randomized_quicksort.ml";
 prebuilt_modules += " vox_sorting_buffer.mli vox_sorting_buffer.ml";
 prebuilt_modules += " vox_fair_coin.mli vox_fair_coin.ml";
 readonly_files = "probability_examples_rejected.ml";
 { setup-ocamlc.opt-build-env; run-expect; check-program-output; }
 { flags = "-extension refinement_types -principal";
   setup-ocamlc.opt-build-env; run-expect; check-program-output; }
*)


#load "vox_sequence.cmo";;
#load "vox_int_sequence.cmo";;
#load "vox_real.cmo";;
#load "vox_real_credits.cmo";;
#load "vox_quicksort_partition.cmo";;
#load "vox_sort_cost.cmo";;
#load "vox_expectation.cmo";;
#load "vox_harmonic.cmo";;
#load "vox_quicksort_cost.cmo";;
#load "vox_quicksort_average.cmo";;
#load "vox_probability.cmo";;
#load "vox_randomized_quicksort.cmo";;
#load "vox_sorting_buffer.cmo";;
#load "vox_fair_coin.cmo";;

module Buffer = Vox_sorting_buffer;;
module Q = Vox_real;;
module C = Vox_probability.Cost;;
[%%expect{|
module Buffer = Vox_sorting_buffer
module Q = Vox_real
module C = Vox_probability.Cost
|}]

let reuse (buffer : {b : Buffer.t | Buffer.valid b} @ unique) =
  let _ = Buffer.drain buffer in
  Buffer.drain buffer;;
[%%expect{|
Line 3, characters 15-21:
3 |   Buffer.drain buffer;;
                   ^^^^^^
Error: This value is used here, but it has already been used as unique at:
Line 2, characters 23-29:
2 |   let _ = Buffer.drain buffer in
                           ^^^^^^

|}]

let unpaid () =
  let buffer = Buffer.empty () in
  let cost = C.empty () in
  ghost_ (Vox_sequence.length_def []);
  Buffer.push 7 buffer cost;;
[%%expect{|
Line 5, characters 23-27:
5 |   Buffer.push 7 buffer cost;;
                           ^^^^
Error: Refinement could not be proved (counterexample)
File "vox_sorting_buffer.mli", line 39, characters 25-56:
  The refinement is stated here.
|}]

let (ordinary_total @ total stateful)
    (cost : {t : C.token | Q.le (Q.of_bigint 2Z) (C.credits t)}
      @ unique total ghost) =
  Vox_fair_coin.retry cost;;
[%%expect{|
Line 4, characters 2-21:
4 |   Vox_fair_coin.retry cost;;
      ^^^^^^^^^^^^^^^^^^^
Error: The value "Vox_fair_coin.retry" is "partial"
       but is expected to be "total"
         because it is used inside the function at lines 2-4, characters 4-26
         which is expected to be "total".
|}]

let underfunded
    (cost : {t : C.token | C.credits t === Q.of_bigint 1Z}
      @ unique total ghost) =
  Vox_fair_coin.retry cost;;
[%%expect{|
Line 4, characters 22-26:
4 |   Vox_fair_coin.retry cost;;
                          ^^^^
Error: Refinement could not be proved (counterexample)
File "vox_fair_coin.mli", line 12, characters 17-52:
  The refinement is stated here.
|}]
