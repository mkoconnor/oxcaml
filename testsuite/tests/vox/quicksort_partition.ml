(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_int_sequence.mli vox_int_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_quicksort_partition.ml";
 prebuilt_modules += " vox_sort_cost.mli vox_sort_cost.ml";
 prebuilt_modules += " vox_expectation.ml vox_harmonic.ml";
 prebuilt_modules += " vox_quicksort_cost.ml vox_quicksort_average.ml";
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence
module Spec = Vox_quicksort_partition
module Average = Vox_quicksort_average
module C = Vox_real_credits.Make ()

module Compare = struct
  type result = #{ order : int; state : C.token @@ ghost }
  let (compare @ total) (left : int) (right : int)
      (token : {t : C.token | Q.le (Q.of_bigint 1Z) (C.credits t)}
        @ unique total ghost) :
      {r : result |
        (r.#order < 0) = (left < right) &&
        (r.#order = 0) = (left = right) &&
        (r.#order > 0) = (left > right) &&
        C.credits r.#state === Q.sub (C.credits token) (Q.of_bigint 1Z)}
        @ unique =
    let state = C.tick token in
    let order = if left < right then -1 else if left = right then 0 else 1 in
    #{ order; state }
end

module Partition = Spec.Make (C) (Compare)

let (check @ total) (values : int list) (pivot : int) =
  let amount = ghost_ (Q.of_bigint (S.length values)) in
  ghost_ (S.length_def values);
  let token = C.Budget.create amount in
  let #{ Partition.less; same; greater; state } =
    Partition.partition values pivot token in
  ghost_ (
    Average.allocations_nonnegative values values;
    Average.average_bound values;
    let n = S.length values in
    if n > 0Z then (
      (() : {u : unit | Q.le (Q.add (Q.of_bigint (Bigint.sub n 1Z))
        (Vox_expectation.uniform (Average.allocations values values)))
        (Vox_quicksort_cost.budget n)}));
    Spec.partition_lengths values pivot;
    Spec.partition_permutation values pivot;
    Spec.partition_bounds values pivot;
    let () : {u : unit | C.credits state === Q.of_bigint 0Z &&
      P.permutation values (S.append less (S.append same greater)) &&
      P.sorted same && P.all less pivot true && P.all greater pivot false}
      = () in
    ());
  less, same, greater

let () =
  let cases = [ []; [2]; [2; 2; 2]; [3; 1; 2; 3; 2; 1];
    [min_int; 0; max_int; min_int; max_int] ] in
  List.iter (fun values ->
    let sorted = P.sorted_copy values in
    assert (sorted = List.sort Stdlib.compare values);
    for index = 0 to List.length sorted - 1 do
      let k = Bigint.of_int index in
      ghost_ (Spec.rank_bounds sorted k);
      let pivot = P.element sorted k in
      let less, _, greater = check values pivot in
      assert (List.length less <= index);
      assert (List.length greater <= List.length values - 1 - index)
    done;
    for index = -1 to List.length values + 1 do
      match Spec.pick values (Bigint.of_int index) with
      | None -> assert (values = [])
      | Some {Spec.pivot; rest} ->
        assert (List.sort Stdlib.compare values =
          List.sort Stdlib.compare (pivot :: rest));
        if 0 <= index && index < List.length values then
          assert (pivot = List.nth values index)
    done;
    List.iter (fun pivot ->
      let less, same, greater = check values pivot in
      assert (less = List.filter (fun x -> x < pivot) values);
      assert (same = List.filter (fun x -> x = pivot) values);
      assert (greater = List.filter (fun x -> x > pivot) values))
      [min_int; -1; 0; 1; 2; 3; max_int]) cases
