(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml vox_probability.mli";
 prebuilt_modules += " vox_probability.ml";
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module S = Vox_sequence
module E = Vox_expectation
module P = Vox_probability
module C = P.Cost

let (pair_facts @ total) (left : Q.t) (right : Q.t) (index : int) :
    {u : unit | S.length [left; right] = 2Z &&
      (if Q.nonnegative left && Q.nonnegative right then
        Q.all_nonnegative [left; right] else true) &&
      (if 0 <= index && index < 2 then
        E.entry [left; right] (Bigint.of_int index) ===
          (if index = 0 then left else right) else true)} @ ghost = ghost_ (
  S.length_def [left; right]; S.length_def [right]; S.length_def [];
  Q.all_nonnegative_def [left; right]; Q.all_nonnegative_def [right];
  Q.all_nonnegative_def [];
  E.entry_def [left; right] (Bigint.of_int index);
  S.at_def [left; right] (Bigint.of_int index);
  S.at_def [right] (Bigint.sub (Bigint.of_int index) 1Z);
  S.at_def [] (Bigint.sub (Bigint.of_int index) 2Z))

let () =
  let zero = ghost_ (Q.of_bigint 0Z) in
  let one = ghost_ (Q.of_bigint 1Z) in
  let two = ghost_ (Q.of_bigint 2Z) in
  let half = ghost_ (Q.of_fraction 1Z 2Z) in
  let costs = ghost_ [zero; two] in
  let errors = ghost_ [one; zero] in
  ghost_ (
    pair_facts zero two 0; pair_facts one zero 0;
    E.uniform_pair zero two; E.uniform_pair one zero;
    E.pair_mean_def zero two; E.pair_mean_def one zero);
  let index = P.run one half (fun cost error monitor ->
    let #{P.index; cost; error} = P.uniform 2 costs errors cost error in
    ghost_ (pair_facts zero two index; pair_facts one zero index);
    if index = 1 then (
      let cost = C.tick cost in
      let _ = C.tick cost in
      ());
    let good = index <> 0 in
    let {P.monitor; error} = P.checkpoint good monitor error in
    let {P.monitor; error = _} = P.checkpoint good monitor error in
    ghost_ (
      (() : {u : unit | P.failed monitor = (index = 0)}));
    index) in
  assert (0 <= index && index < 2)
