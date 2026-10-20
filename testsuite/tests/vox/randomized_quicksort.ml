(* TEST
 has-z3;
 flags = "-extension refinement_types -principal -vox-probabilistic";
 use_runtime = "false";
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
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module S = Vox_sequence
module B = Vox_quicksort_cost
module P = Vox_probability
module C = P.Cost

let[@def] rec budget (cases : int list list) = ghost_ (
  match cases with
  | [] -> Q.of_bigint 0Z
  | values :: rest -> Q.add (B.budget (S.length values)) (budget rest))

let rec (nonnegative @ total) (cases : int list list) :
    {u : unit | Q.nonnegative (budget cases)} @ ghost = ghost_ (
  budget_def cases;
  match cases with
  | [] -> ()
  | values :: rest ->
    S.length_def values;
    B.nonnegative (S.length values);
    nonnegative rest)

let rec check : (cases : int list list) ->
    {t : C.token | Q.le (budget cases) (C.credits t)}
      @ unique total ghost -> unit = fun cases cost ->
  ghost_ (budget_def cases);
  match cases with
  | [] -> ()
  | values :: rest ->
    let amount = ghost_ (B.budget (S.length values)) in
    ghost_ (
      S.length_def values; B.nonnegative (S.length values);
      nonnegative rest);
    let {C.left; right} = C.split amount cost in
    if S.length values <= Bigint.of_int max_int then (
      let #{Vox_randomized_quicksort.values = sorted; cost = _} =
        Vox_randomized_quicksort.sort values left in
      assert (sorted = List.sort Stdlib.compare values));
    check rest right

let () =
  let cases =
    [ []; [1]; [2; 1]; [3; 1; 2; 3; 2; 1];
      [2; 3; 1; 4; 5]; [min_int; max_int; 0; min_int; max_int];
      List.init 50 (fun i -> i); List.init 50 (fun i -> 50 - i);
      List.init 50 (fun _ -> 7); List.init 50 (fun i -> i mod 5) ] in
  let cases = List.concat (List.init 20 (fun _ -> cases)) in
  let amount = ghost_ (budget cases) in
  let zero = ghost_ (Q.of_bigint 0Z) in
  ghost_ (nonnegative cases);
  P.run amount zero (fun cost _error _monitor -> check cases cost)
