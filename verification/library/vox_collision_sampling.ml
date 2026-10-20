module Q = Vox_real
module S = Vox_sequence
module E = Vox_expectation
module P = Vox_probability
module C = P.Error
module B = Vox_collision_bound

let[@def] rec count (seen : int list) (value : Bigint.t) =
  match seen with
  | [] -> 0Z
  | head :: tail -> Bigint.add
      (if Bigint.of_int head = value then 1Z else 0Z) (count tail value)

let rec (count_nonnegative @ total) (seen : int list) (value : Bigint.t) :
    {u : unit | 0Z <= count seen value} =
  count_def seen value;
  match seen with [] -> () | _ :: tail -> count_nonnegative tail value

let[@def] rec distinct (seen : int list) =
  match seen with
  | [] -> true
  | head :: tail -> count tail (Bigint.of_int head) = 0Z && distinct tail

let (distinct_empty @ total) () : {u : unit | distinct []} =
  distinct_def []; ()

let[@def] rec in_range (size : int) (values : int list) =
  match values with
  | [] -> true
  | head :: tail -> 0 <= head && head < size && in_range size tail

let rec (prefix_extend @ total) (size : int) (values : int list)
    (count : {n : Bigint.t | 0Z <= n}) (last : int) (suffix : int list) :
    {u : unit | if in_range size (S.take count values) &&
      S.drop count values === last :: suffix && 0 <= last && last < size
      then in_range size (S.take (Bigint.add count 1Z) values) &&
        S.drop (Bigint.add count 1Z) values === suffix else true} =
  S.take_def count values; S.take_def (Bigint.add count 1Z) values;
  S.drop_def count values; S.drop_def (Bigint.add count 1Z) values;
  in_range_def size (S.take count values);
  in_range_def size (S.take (Bigint.add count 1Z) values);
  match values with
  | [] -> ()
  | _ :: tail ->
    if count = 0Z then (
      S.take_def 0Z tail; S.drop_def 0Z tail; in_range_def size [])
    else prefix_extend size tail (Bigint.sub count 1Z) last suffix

let[@def] rec range_count (seen : int list) (first : Bigint.t)
    (past : Bigint.t) =
  match seen with
  | [] -> 0Z
  | head :: tail -> Bigint.add
      (if first <= Bigint.of_int head && Bigint.of_int head < past
        then 1Z else 0Z) (range_count tail first past)

let rec (range_bounds @ total) (seen : int list) (first : Bigint.t)
    (past : Bigint.t) :
    {u : unit | 0Z <= range_count seen first past &&
      range_count seen first past <= S.length seen &&
      (if past <= first then range_count seen first past = 0Z else true)} =
  range_count_def seen first past; S.length_def seen;
  match seen with [] -> () | _ :: tail -> range_bounds tail first past

let rec (range_step @ total) (seen : int list) (first : Bigint.t)
    (past : {n : Bigint.t | first < n}) :
    {u : unit | range_count seen first past =
      Bigint.add (count seen first)
        (range_count seen (Bigint.add first 1Z) past)} =
  range_count_def seen first past;
  range_count_def seen (Bigint.add first 1Z) past;
  count_def seen first;
  match seen with [] -> () | _ :: tail -> range_step tail first past

let[@def] rec table (seen : int list) (first : Bigint.t)
    (size : Bigint.t) = ghost_ (
  if size <= 0Z then [] else
    Q.of_bigint (count seen first) ::
      table seen (Bigint.add first 1Z) (Bigint.sub size 1Z))
[@@decreases let n : Bigint.t = size in if n > 0Z then n else 0Z]

let rec (table_facts @ total) (seen : int list) (first : Bigint.t)
    (size : {n : Bigint.t | 0Z <= n}) :
    {u : unit | S.length (table seen first size) = size &&
      Q.all_nonnegative (table seen first size) &&
      Q.sum (table seen first size) ===
        Q.of_bigint (range_count seen first (Bigint.add first size))}
    @ ghost = ghost_ (
  table_def seen first size;
  S.length_def (table seen first size);
  Q.all_nonnegative_def (table seen first size);
  Q.sum_def (table seen first size);
  range_bounds seen first (Bigint.add first size);
  if size > 0Z then (
    table_facts seen (Bigint.add first 1Z) (Bigint.sub size 1Z);
    range_step seen first (Bigint.add first size);
    count_nonnegative seen first);
  ())
[@@decreases size]

let rec (table_at @ total) (seen : int list) (first : Bigint.t)
    (size : {n : Bigint.t | 0Z <= n})
    (index : {n : Bigint.t | 0Z <= n && n < size}) :
    {u : unit | E.entry (table seen first size) index ===
      Q.of_bigint (count seen (Bigint.add first index))} @ ghost = ghost_ (
  table_def seen first size;
  E.entry_def (table seen first size) index;
  S.at_def (table seen first size) index;
  if index > 0Z then (
    table_at seen (Bigint.add first 1Z) (Bigint.sub size 1Z)
      (Bigint.sub index 1Z);
    E.entry_def (table seen (Bigint.add first 1Z) (Bigint.sub size 1Z))
      (Bigint.sub index 1Z));
  ())
[@@decreases size]

let (table_mean @ total) (seen : int list) (size : Q.positive) :
    {u : unit | Q.le (E.uniform (table seen 0Z size))
      (Q.divide (Q.of_bigint (S.length seen)) size)} @ ghost = ghost_ (
  table_facts seen 0Z size;
  table_def seen 0Z size; E.uniform_def (table seen 0Z size);
  range_bounds seen 0Z size)

let[@def] domain (size : int) : Q.positive =
  if size > 0 then Bigint.of_int size else 1Z

type sample = #{ values : int list @@ aliased; monitor : P.monitor @@ ghost }

let rec (draw_paid @ total stateful) (size : {n : int | 0 < n})
    (draws : {n : int | 0 <= n}) (seen : int list)
    (monitor : {m : P.monitor | P.failed m || distinct seen}
      @ unique total ghost)
    (error : {t : C.token | Q.le
      (B.additional (S.length seen) (Bigint.of_int draws)
        (domain size)) (C.credits t)} @ unique total ghost) :
    {r : sample | (P.failed r.#monitor || distinct r.#values) &&
      (if P.failed monitor then P.failed r.#monitor else true) &&
      S.length r.#values = Bigint.add (S.length seen) (Bigint.of_int draws) &&
      S.drop (Bigint.of_int draws) r.#values === seen &&
      in_range size (S.take (Bigint.of_int draws) r.#values)}
      @ unique =
  ghost_ (domain_def size);
  if draws = 0 then (
    ghost_ (S.drop_def 0Z seen; S.take_def 0Z seen; in_range_def size []);
    #{values = seen; monitor}) else (
    let n = ghost_ (S.length seen) in
    let immediate = ghost_ (Q.divide (Q.of_bigint n) (Bigint.of_int size)) in
    ghost_ (
      S.length_def seen;
      B.nonnegative (Bigint.add n 1Z)
        (Bigint.sub (Bigint.of_int draws) 1Z) (Bigint.of_int size);
      B.step n (Bigint.of_int draws) (Bigint.of_int size));
    let {C.left = payment; right = reserve} = C.split immediate error in
    let allocations = ghost_ (table seen 0Z (Bigint.of_int size)) in
    ghost_ (table_facts seen 0Z (Bigint.of_int size);
      table_mean seen (Bigint.of_int size));
    let #{P.index; error} = P.uniform_error size allocations payment in
    let good = ghost_ (count seen (Bigint.of_int index) = 0Z) in
    ghost_ (
      table_at seen 0Z (Bigint.of_int size) (Bigint.of_int index);
      count_nonnegative seen (Bigint.of_int index));
    let {P.monitor; error = _} = P.checkpoint good monitor error in
    let extended = index :: seen in
    ghost_ (distinct_def extended; S.length_def extended);
    let #{values; monitor} =
      draw_paid size (draws - 1) extended monitor reserve in
    ghost_ (prefix_extend size values
      (Bigint.sub (Bigint.of_int draws) 1Z) index seen);
    #{values; monitor})
[@@decreases Bigint.of_int draws]

type result =
  #{ values : int list @@ aliased; monitor : P.monitor @@ ghost;
     error : C.token @@ ghost }

let (draw @ total stateful) (size : {n : int | 0 < n})
    (draws : {n : int | 0 <= n}) (seen : int list)
    (monitor : {m : P.monitor | P.failed m || distinct seen}
      @ unique total ghost)
    (error : {t : C.token | Q.le
      (B.additional (S.length seen) (Bigint.of_int draws) (domain size))
      (C.credits t)} @ unique total ghost) :
    {r : result | (P.failed r.#monitor || distinct r.#values) &&
      (if P.failed monitor then P.failed r.#monitor else true) &&
      S.length r.#values = Bigint.add (S.length seen) (Bigint.of_int draws) &&
      S.drop (Bigint.of_int draws) r.#values === seen &&
      in_range size (S.take (Bigint.of_int draws) r.#values) &&
      C.credits r.#error === Q.sub (C.credits error)
        (B.additional (S.length seen) (Bigint.of_int draws) (domain size))}
      @ unique =
  let amount = ghost_ (
    B.additional (S.length seen) (Bigint.of_int draws) (domain size)) in
  ghost_ (
    S.length_def seen;
    B.nonnegative (S.length seen) (Bigint.of_int draws) (domain size));
  let {C.left; right = error} = C.split amount error in
  let (#{values; monitor} : sample) =
    draw_paid size draws seen monitor left in
  #{values; monitor; error}
