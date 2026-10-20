(* TEST
 has-z3;
 flags = "-extension refinement_types -principal -vox-probabilistic";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml vox_probability.mli";
 prebuilt_modules += " vox_probability.ml";
 prebuilt_modules += " vox_collision_bound.ml vox_collision_sampling.mli";
 prebuilt_modules += " vox_collision_sampling.ml";
 use_runtime = "false";
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module S = Vox_sequence
module P = Vox_probability
module C = P.Error
module B = Vox_collision_bound
module Sample = Vox_collision_sampling

let () =
  let total = ghost_ (B.collisions 8Z 64Z) in
  let zero = ghost_ (Q.of_bigint 0Z) in
  ghost_ (
    Sample.domain_def 64; B.collisions_def 8Z 64Z; B.compose 0Z 4Z 4Z 64Z;
    B.nonnegative 0Z 4Z 64Z; B.nonnegative 4Z 4Z 64Z;
    B.nonnegative 0Z 8Z 64Z);
  let values = P.run zero total (fun _cost error monitor ->
    ghost_ (Sample.distinct_empty (); S.length_def []);
    let #{Sample.values = initial; monitor; error} =
      Sample.draw 64 4 [] monitor error in
    let #{Sample.values; monitor; error} =
      Sample.draw 64 4 initial monitor error in
    ghost_ (
      (() : {u : unit | S.drop 4Z values === initial &&
        Sample.in_range 64 (S.take 4Z values)});
      Sample.count_def [] 1000Z; Sample.distinct_def [];
      Sample.distinct_def [1000]; S.length_def [];
      S.length_def [1000]; B.empty 1Z 64Z;
      C.nonnegative (borrow_ error));
    let #{Sample.values = preserved; monitor = _; error = _} =
      Sample.draw 64 0 [1000] monitor error in
    ghost_ (S.drop_def 0Z preserved;
      (() : {u : unit | preserved === [1000]}));
    assert (preserved = [1000]);
    values) in
  assert (List.length values = 8);
  assert (List.for_all (fun n -> 0 <= n && n < 64) values)
