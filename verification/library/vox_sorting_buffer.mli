module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence
module C = Vox_probability.Cost
module B = Vox_quicksort_cost
module Log = Vox_sort_cost

type t : value mod logical
type step = #{ buffer : t; cost : C.token @@ ghost }

val contents : t @ local immutable total ghost forkable unyielding ->
  int list @ ghost @@ total
val potential : t @ local immutable total ghost forkable unyielding ->
  Q.t @ ghost @@ total
val fee : t @ local immutable total ghost forkable unyielding ->
  Q.t @ ghost @@ total
val valid : t @ local immutable total ghost forkable unyielding ->
  bool @ ghost @@ total

val potential_law :
  (buffer : t) @ local immutable total ghost forkable unyielding ->
  {u : unit | if valid buffer then
    potential buffer === B.budget (S.length (contents buffer)) &&
    S.length (contents buffer) <= Bigint.of_int max_int else true} @@ total

(** Each insertion deposits the increase in the expected sorting budget.
    The fee is logarithmic in the resulting number of elements. *)
val fee_law : (buffer : t) @ local immutable total ghost forkable unyielding ->
  {u : unit | fee buffer === B.deposit (S.length (contents buffer)) &&
      Q.nonnegative (fee buffer) && Q.le (fee buffer)
    (Q.of_bigint (Bigint.mul 2Z (Bigint.add 2Z
      (Log.height (Bigint.add (S.length (contents buffer)) 1Z)))))} @@ total

val empty : unit -> {b : t | valid b && contents b === []} @ unique @@ total

val push : (value : int) ->
  (buffer : {b : t | valid b &&
    S.length (contents b) < Bigint.of_int max_int}) @ unique ->
  (cost : {t : C.token | Q.le (fee buffer) (C.credits t)})
    @ unique total ghost ->
  {r : step | valid r.#buffer &&
    contents r.#buffer === value :: contents buffer &&
    C.credits r.#cost === Q.sub (C.credits cost) (fee buffer)} @ unique @@ total

(** Sorting consumes the stored potential and needs no external credits.
    The bound counts comparisons, under [Vox_probability]'s assumptions. *)
val drain : (buffer : {b : t | valid b}) @ unique ->
  {values : int list | P.sorted values &&
    P.permutation (contents buffer) values &&
    S.length values = S.length (contents buffer)} @@ total stateful
