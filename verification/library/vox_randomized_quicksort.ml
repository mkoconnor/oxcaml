module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence
module E = Vox_expectation
module Probability = Vox_probability
module C = Probability.Cost
module Bound = Vox_quicksort_cost
module Average = Vox_quicksort_average
module Spec = Vox_quicksort_partition

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
    let order = Stdlib.compare left right in
    #{order; state}
end

module Partition = Spec.Make (C) (Compare)

let rec (length @ total)
    (values : {v : int list | S.length v <= Bigint.of_int max_int}) :
    {n : int | 0 <= n && Bigint.of_int n = S.length values} =
  ghost_ (S.length_def values);
  match values with
  | [] -> 0
  | _ :: tail ->
    ghost_ (S.length_def tail);
    let n = length tail in
    n + 1

let rec (core @ total stateful)
    (values : {v : int list | S.length v <= Bigint.of_int max_int})
    (cost : {t : C.token |
      Q.le (Bound.budget (S.length values)) (C.credits t)}
      @ unique total ghost) :
    {result : int list | P.sorted result && P.permutation values result &&
      S.length result = S.length values} =
  let size = length values in
  ghost_ (S.length_def values; Bound.nonnegative (S.length values));
  let {C.left = cost; right = _} =
    C.split (ghost_ (Bound.budget (S.length values))) cost in
  if size <= 1 then (
    ghost_ (P.sorted_short values; P.permutation_refl values);
    values)
  else (
    let allocations = ghost_ (Average.allocations values values) in
    let reserve = ghost_ (Q.of_bigint (Bigint.sub (S.length values) 1Z)) in
    ghost_ (
      Average.allocations_length values values;
      Average.allocations_nonnegative values values;
      Average.average_bound values; Average.remaining_bound values;
      E.uniform_nonnegative allocations);
    let {C.left = partition_cost; right = cost} = C.split reserve cost in
    let #{Probability.index; cost} =
      Probability.uniform_cost size allocations cost in
    match Spec.pick values (Bigint.of_int index) with
    | None ->
      ghost_ (P.sorted_short values; P.permutation_refl values);
      values
    | Some {Spec.pivot; rest} ->
      ghost_ (
        Average.allocations_at values values (Bigint.of_int index);
        E.entry_def allocations (Bigint.of_int index);
        Average.picked_children values pivot rest;
        Average.children_def values pivot; Average.children_def rest pivot);
      let #{Partition.less; same; greater; state = _} =
        Partition.partition rest pivot partition_cost in
      let left_budget = ghost_ (Bound.budget (S.length less)) in
      ghost_ (
        Spec.select_length rest pivot Spec.Less;
        Spec.select_length rest pivot Spec.Greater;
        Spec.partition_lengths rest pivot;
        Spec.partition_bounds rest pivot;
        Bound.nonnegative (S.length less);
        Bound.nonnegative (S.length greater));
      let {C.left = left_cost; right = right_cost} =
        C.split left_budget cost in
      let left = core less left_cost in
      let right = core greater right_cost in
      let result = Spec.join left same right pivot in
      ghost_ (
        P.all_permutation less left pivot true;
        P.all_permutation greater right pivot false;
        Spec.join_sorted left same right pivot;
        Spec.join_permutation rest pivot left right;
        P.permutation_trans values (pivot :: rest) result;
        P.permutation_length values result);
      result)
[@@decreases S.length values]

type result = #{ values : int list @@ aliased; cost : C.token @@ ghost }

let (sort @ total stateful)
    (values : {v : int list | S.length v <= Bigint.of_int max_int})
    (cost : {t : C.token |
      Q.le (Bound.budget (S.length values)) (C.credits t)}
      @ unique total ghost) :
    {r : result | P.sorted r.#values && P.permutation values r.#values &&
      S.length r.#values = S.length values &&
      C.credits r.#cost ===
        Q.sub (C.credits cost) (Bound.budget (S.length values))} @ unique =
  ghost_ (S.length_def values; Bound.nonnegative (S.length values));
  let amount = ghost_ (Bound.budget (S.length values)) in
  let {C.left = work; right = cost} = C.split amount cost in
    let values = core values work in
  #{values; cost}
