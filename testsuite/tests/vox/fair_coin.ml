(* TEST
 has-z3;
 flags = "-extension refinement_types -principal -vox-probabilistic";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml vox_probability.mli";
 prebuilt_modules += " vox_probability.ml";
 prebuilt_modules += " vox_geometric_cost.ml vox_fair_coin.mli";
 prebuilt_modules += " vox_fair_coin.ml";
 use_runtime = "false";
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module P = Vox_probability

let () =
  let two = ghost_ (Q.of_bigint 2Z) in
  let zero = ghost_ (Q.of_bigint 0Z) in
  P.run two zero (fun cost _error _monitor -> Vox_fair_coin.retry cost)
