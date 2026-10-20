module Q = Vox_real
module S = Vox_sequence
module E = Vox_expectation

module Cost : Vox_real_credits.S
module Error : Vox_real_credits.S

type monitor : void mod logical

val failed : monitor @ local immutable total ghost -> bool @ ghost @@ total

type checkpoint =
  { monitor : monitor @@ ghost; error : Error.token @@ ghost }

(** Records the first failure, charging one error credit. All paths remain
    subject to ordinary verification. *)
val checkpoint : (good : bool) @ ghost ->
  (monitor : monitor) @ unique total ghost ->
  (error : {t : Error.token | good || failed monitor ||
    Q.le (Q.of_bigint 1Z) (Error.credits t)}) @ unique total ghost ->
  {r : checkpoint | failed r.monitor = (failed monitor || not good) &&
    Error.credits r.error === Q.sub (Error.credits error)
      (Q.of_bigint (if good || failed monitor then 0Z else 1Z))}
    @ unique @@ total

type sample =
  #{ index : int; cost : Cost.token @@ ghost; error : Error.token @@ ghost }

(** The semantic model assumes fresh conditional uniformity and atomic
    completion. The executable backend uses [Random.full_int]; its range
    contract alone does not establish either probabilistic assumption.
    Sampling consumes the supplied tokens and returns the selected table
    entries. Split off any surplus credits before calling a sampler. *)
val uniform : (bound : {n : int | 0 < n}) ->
  (cost_alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
    Q.all_nonnegative qs}) @ ghost ->
  (error_alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
    Q.all_nonnegative qs}) @ ghost ->
  (cost : {t : Cost.token | Q.le (E.uniform cost_alloc) (Cost.credits t)})
    @ unique total ghost ->
  (error : {t : Error.token | Q.le (E.uniform error_alloc) (Error.credits t)})
    @ unique total ghost ->
  {r : sample | 0 <= r.#index && r.#index < bound &&
    Cost.credits r.#cost === E.entry cost_alloc (Bigint.of_int r.#index) &&
    Error.credits r.#error === E.entry error_alloc (Bigint.of_int r.#index)}
    @ unique @@ total stateful

type cost_sample = #{ index : int; cost : Cost.token @@ ghost }

val uniform_cost : (bound : {n : int | 0 < n}) ->
  (alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
    Q.all_nonnegative qs}) @ ghost ->
  (cost : {t : Cost.token | Q.le (E.uniform alloc) (Cost.credits t)})
    @ unique total ghost ->
  {r : cost_sample | 0 <= r.#index && r.#index < bound &&
    Cost.credits r.#cost === E.entry alloc (Bigint.of_int r.#index)}
    @ unique @@ total stateful

type error_sample = #{ index : int; error : Error.token @@ ghost }

val uniform_error : (bound : {n : int | 0 < n}) ->
  (alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
    Q.all_nonnegative qs}) @ ghost ->
  (error : {t : Error.token | Q.le (E.uniform alloc) (Error.credits t)})
    @ unique total ghost ->
  {r : error_sample | 0 <= r.#index && r.#index < bound &&
    Error.credits r.#error === E.entry alloc (Bigint.of_int r.#index)}
    @ unique @@ total stateful

(** A bound requires linking the complete executable with
    [-vox-probabilistic]. Initial issuance must be one direct call during
    module initialization. Budgets are fixed at entry to this call.

    Conditional on the entry history, the accounting argument maintains,
    at every finite execution prefix:
    E[charged cost + outstanding cost credits] <= initial cost budget, and
    E[first-failure indicator + outstanding error credits] <= initial error
    budget. Outstanding credits include stored and separately held tokens.
    Splitting and merging preserve each sum; discarding decreases it. A tick
    transfers one cost credit to charged cost. The first failed checkpoint
    transfers one error credit to the failure indicator. Sampling cannot
    increase either conditional expectation because its allocation table is
    fixed before a fresh uniform outcome is drawn.

    Monotone convergence bounds total charged cost and the probability of
    ever recording failure, including unbounded executions. Finite expected
    cost implies almost-sure termination only when every divergent execution
    incurs infinitely many charged events. These are bounds on explicit
    charged events, not wall-clock time. Failure does not imply [false] in
    the proof context; exact cost and totality obligations remain in force.

    This is a semantic accounting argument under the stated sampler and
    compiler assumptions, not a mechanized compiler adequacy theorem. *)
val run : (cost : {q : Q.t | Q.nonnegative q}) @ ghost ->
  (error : {q : Q.t | Q.nonnegative q}) @ ghost ->
  ((cost : {t : Cost.token | Cost.credits t === cost})
      @ unique total ghost ->
    (error : {t : Error.token | Error.credits t === error})
      @ unique total ghost ->
    {m : monitor | not (failed m)} @ unique total ghost -> 'a) @ local once ->
  'a
