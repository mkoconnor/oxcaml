module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence
module C = Vox_probability.Cost
module Bound = Vox_quicksort_cost

type result = #{ values : int list @@ aliased; cost : C.token @@ ghost }

(** Counts calls to the integer key comparator. Totality is relative to the
    atomic sampler assumption in [Vox_probability]. The returned credits
    exclude the reserved sorting budget, regardless of the realized cost. *)
val sort :
  (values : {v : int list | S.length v <= Bigint.of_int max_int}) ->
  (cost : {t : C.token | Q.le (Bound.budget (S.length values)) (C.credits t)})
    @ unique total ghost ->
  {r : result | P.sorted r.#values && P.permutation values r.#values &&
    S.length r.#values = S.length values &&
    C.credits r.#cost ===
      Q.sub (C.credits cost) (Bound.budget (S.length values))}
    @ unique @@ total stateful
