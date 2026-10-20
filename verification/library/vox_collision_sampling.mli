module Q = Vox_real
module S = Vox_sequence
module C = Vox_probability.Error
module B = Vox_collision_bound

val count : int list -> Bigint.t -> Bigint.t @@ total
val count_def : (values : int list) -> (value : Bigint.t) ->
  {u : unit | count values value ===
    (match values with [] -> 0Z | head :: tail -> Bigint.add
      (if Bigint.of_int head = value then 1Z else 0Z) (count tail value))}
  @@ total
val distinct : int list -> bool @@ total
val distinct_def : (values : int list) ->
  {u : unit | distinct values === (match values with [] -> true
    | head :: tail -> count tail (Bigint.of_int head) = 0Z && distinct tail)}
  @@ total
val distinct_empty : unit -> {u : unit | distinct []} @@ total
val in_range : int -> int list -> bool @@ total
val in_range_def : (size : int) -> (values : int list) ->
  {u : unit | in_range size values === (match values with [] -> true
    | head :: tail -> 0 <= head && head < size && in_range size tail)}
  @@ total
val domain : int -> Q.positive @@ total
val domain_def : (size : int) ->
  {u : unit | domain size = (if size > 0 then Bigint.of_int size else 1Z)}
  @@ total

type result =
  #{ values : int list @@ aliased;
     monitor : Vox_probability.monitor @@ ghost; error : C.token @@ ghost }

(** Each call draws [draws] fresh uniform values and prepends them to [seen].
    Its additional error budget is d * (2 * s + d - 1) / (2 * size),
    where s is the length of [seen] and d is [draws]. Excess error credits and
    the monitor are returned for later calls. Under [Vox_probability]'s
    assumptions, the initial error budget bounds the probability of any
    duplicate. *)
val draw : (size : {n : int | 0 < n}) ->
  (draws : {n : int | 0 <= n}) -> (seen : int list) ->
  (monitor : {m : Vox_probability.monitor |
    Vox_probability.failed m || distinct seen}) @ unique total ghost ->
  (error : {t : C.token | Q.le
    (B.additional (S.length seen) (Bigint.of_int draws) (domain size))
    (C.credits t)}) @ unique total ghost ->
  {r : result |
    (Vox_probability.failed r.#monitor || distinct r.#values) &&
    (if Vox_probability.failed monitor then
      Vox_probability.failed r.#monitor else true) &&
    S.length r.#values = Bigint.add (S.length seen) (Bigint.of_int draws) &&
    S.drop (Bigint.of_int draws) r.#values === seen &&
    in_range size (S.take (Bigint.of_int draws) r.#values) &&
    C.credits r.#error === Q.sub (C.credits error)
      (B.additional (S.length seen) (Bigint.of_int draws) (domain size))}
    @ unique @@ total stateful
