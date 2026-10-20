module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence
module C = Vox_probability.Cost
module B = Vox_quicksort_cost
module Log = Vox_sort_cost

type t = { items : int list @@ global; bank : C.token @@ ghost }
type step = #{ buffer : t; cost : C.token @@ ghost }

let[@def] contents
    (buffer : t @ local immutable total ghost forkable unyielding) =
  ghost_ buffer.items
let[@def] potential
    (buffer : t @ local immutable total ghost forkable unyielding) =
  ghost_ (C.credits buffer.bank)
let[@def] fee (buffer : t @ local immutable total ghost forkable unyielding) =
  ghost_ (B.deposit (S.length (contents buffer)))
let[@def] valid
    (buffer : t @ local immutable total ghost forkable unyielding) = ghost_ (
  S.length (contents buffer) <= Bigint.of_int max_int &&
  potential buffer === B.budget (S.length (contents buffer)))

let (potential_law @ total)
    (buffer : t @ local immutable total ghost forkable unyielding) :
    {u : unit | if valid buffer then
      potential buffer === B.budget (S.length (contents buffer)) &&
      S.length (contents buffer) <= Bigint.of_int max_int else true} =
  ghost_ (valid_def buffer);
  ()

let (fee_law @ total)
    (buffer : t @ local immutable total ghost forkable unyielding) :
    {u : unit | fee buffer === B.deposit (S.length (contents buffer)) &&
      Q.nonnegative (fee buffer) && Q.le (fee buffer)
      (Q.of_bigint (Bigint.mul 2Z (Bigint.add 2Z
        (Log.height (Bigint.add (S.length (contents buffer)) 1Z)))))} =
  ghost_ (
    fee_def buffer; S.length_def (contents buffer);
    B.deposit_funds_next (S.length (contents buffer));
    B.deposit_bound (S.length (contents buffer)));
  ()

let (empty @ total) () : {b : t | valid b && contents b === []} @ unique =
  let bank = C.empty () in
  let buffer = {items = []; bank} in
  ghost_ (
    contents_def (borrow_ buffer); potential_def (borrow_ buffer);
    valid_def (borrow_ buffer); S.length_def [];
    B.budget_def 0Z; Vox_harmonic.harmonic_def 0Z);
  buffer

let (push @ total) (value : int)
    (buffer : {b : t | valid b &&
      S.length (contents b) < Bigint.of_int max_int} @ unique)
    (cost : {t : C.token | Q.le (fee buffer) (C.credits t)}
      @ unique total ghost) :
    {r : step | valid r.#buffer &&
      contents r.#buffer === value :: contents buffer &&
      C.credits r.#cost === Q.sub (C.credits cost) (fee buffer)} @ unique =
  let amount = ghost_ (fee (borrow_ buffer)) in
  ghost_ (
    fee_law (borrow_ buffer); fee_def (borrow_ buffer);
    valid_def (borrow_ buffer); contents_def (borrow_ buffer);
    potential_def (borrow_ buffer));
  let {C.left = deposit; right = cost} = C.split amount cost in
  let {items; bank} = buffer in
  ghost_ (
    S.length_def items; B.deposit_funds_next (S.length items));
  let bank = C.merge bank deposit in
  let items = value :: items in
  let buffer = {items; bank} in
  ghost_ (
    S.length_def items; contents_def (borrow_ buffer);
    potential_def (borrow_ buffer); valid_def (borrow_ buffer));
  #{buffer; cost}

let (drain @ total stateful) (buffer : {b : t | valid b} @ unique) :
    {values : int list | P.sorted values &&
      P.permutation (contents buffer) values &&
      S.length values = S.length (contents buffer)} =
  ghost_ (
    valid_def (borrow_ buffer); contents_def (borrow_ buffer);
    potential_def (borrow_ buffer));
  let {items; bank} = buffer in
  let #{Vox_randomized_quicksort.values; cost = _} =
    Vox_randomized_quicksort.sort items bank in
  values
