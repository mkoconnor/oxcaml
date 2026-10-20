module Q = Vox_real
module S = Vox_sequence
module E = Vox_expectation

module Cost = Vox_real_credits.Make ()
module Error = Vox_real_credits.Make ()

type monitor = { seen : bool @@ ghost global total contended }

let[@def] failed (monitor : monitor @ local immutable total ghost) =
  ghost_ monitor.seen

type checkpoint =
  { monitor : monitor @@ ghost; error : Error.token @@ ghost }

let (checkpoint @ total) (good : bool @ ghost)
    (monitor : monitor @ unique total ghost)
    (error : {t : Error.token | good || failed monitor ||
      Q.le (Q.of_bigint 1Z) (Error.credits t)} @ unique total ghost) :
    {r : checkpoint | failed r.monitor = (failed monitor || not good) &&
      Error.credits r.error === Q.sub (Error.credits error)
        (Q.of_bigint (if good || failed monitor then 0Z else 1Z))} @ unique =
  let charge = ghost_ (
    Q.of_bigint (if good || failed (borrow_ monitor) then 0Z else 1Z)) in
  ghost_ (
    Error.nonnegative (borrow_ error));
  let {Error.left = _; right = error} = Error.split charge error in
  let next = {seen = ghost_ (failed monitor || not good)} in
  ghost_ (failed_def (borrow_ next));
  {monitor = next; error}

external sampler_contract : (int -> int) ->
  ((bound : {n : int | 0 < n}) -> {i : int | 0 <= i && i < bound})
    @ total stateful = "%identity"

let draw = sampler_contract Random.full_int

type sample =
  #{ index : int; cost : Cost.token @@ ghost; error : Error.token @@ ghost }

let (uniform @ total stateful) (bound : {n : int | 0 < n})
    (cost_alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
      Q.all_nonnegative qs} @ ghost)
    (error_alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
      Q.all_nonnegative qs} @ ghost)
    (_cost : {t : Cost.token |
      Q.le (E.uniform cost_alloc) (Cost.credits t)} @ unique total ghost)
    (_error : {t : Error.token |
      Q.le (E.uniform error_alloc) (Error.credits t)} @ unique total ghost) :
    {r : sample | 0 <= r.#index && r.#index < bound &&
      Cost.credits r.#cost === E.entry cost_alloc (Bigint.of_int r.#index) &&
      Error.credits r.#error === E.entry error_alloc (Bigint.of_int r.#index)}
      @ unique =
  let index = draw bound in
  let cost = ghost_ (
    E.entry_nonnegative cost_alloc (Bigint.of_int index);
    Cost.Budget.create (E.entry cost_alloc (Bigint.of_int index))) in
  let error = ghost_ (
    E.entry_nonnegative error_alloc (Bigint.of_int index);
    Error.Budget.create (E.entry error_alloc (Bigint.of_int index))) in
  #{index; cost; error}

type cost_sample = #{ index : int; cost : Cost.token @@ ghost }

let (uniform_cost @ total stateful) (bound : {n : int | 0 < n})
    (alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
      Q.all_nonnegative qs} @ ghost)
    (cost : {t : Cost.token | Q.le (E.uniform alloc) (Cost.credits t)}
      @ unique total ghost) :
    {r : cost_sample | 0 <= r.#index && r.#index < bound &&
      Cost.credits r.#cost === E.entry alloc (Bigint.of_int r.#index)}
      @ unique =
  let zeros = ghost_ (E.zeros (Bigint.of_int bound)) in
  ghost_ (
    E.zeros_facts (Bigint.of_int bound);
    E.zeros_mean (Bigint.of_int bound));
  let error = Error.empty () in
  let #{index; cost; error = _} = uniform bound alloc zeros cost error in
  #{index; cost}

type error_sample = #{ index : int; error : Error.token @@ ghost }

let (uniform_error @ total stateful) (bound : {n : int | 0 < n})
    (alloc : {qs : Q.t list | S.length qs = Bigint.of_int bound &&
      Q.all_nonnegative qs} @ ghost)
    (error : {t : Error.token | Q.le (E.uniform alloc) (Error.credits t)}
      @ unique total ghost) :
    {r : error_sample | 0 <= r.#index && r.#index < bound &&
      Error.credits r.#error === E.entry alloc (Bigint.of_int r.#index)}
      @ unique =
  let zeros = ghost_ (E.zeros (Bigint.of_int bound)) in
  ghost_ (
    E.zeros_facts (Bigint.of_int bound);
    E.zeros_mean (Bigint.of_int bound));
  let cost = Cost.empty () in
  let #{index; cost = _; error} = uniform bound zeros alloc cost error in
  #{index; error}

let run (cost : {q : Q.t | Q.nonnegative q} @ ghost)
    (error : {q : Q.t | Q.nonnegative q} @ ghost)
    (body :
      ({t : Cost.token | Cost.credits t === cost} @ unique total ghost ->
        {t : Error.token | Error.credits t === error} @ unique total ghost ->
        {m : monitor | not (failed m)} @ unique total ghost -> 'a)
      @ local once) =
  let cost = Cost.Budget.create cost in
  let error = Error.Budget.create error in
  let monitor = {seen = ghost_ false} in
  ghost_ (failed_def (borrow_ monitor));
  body cost error monitor
