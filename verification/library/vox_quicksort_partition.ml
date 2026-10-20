module Q = Vox_real
module S = Vox_sequence
module P = Vox_int_sequence

type relation = Less | Equal | Greater

let[@def] belongs (value : int) (pivot : int) (side : relation) =
  match side with
  | Less -> value < pivot
  | Equal -> value = pivot
  | Greater -> pivot < value

let[@def] rec select (values : int list) (pivot : int) (side : relation) =
  match values with
  | [] -> []
  | head :: tail ->
    if belongs head pivot side then head :: select tail pivot side
    else select tail pivot side

let rec (select_length @ total) (values : int list) (pivot : int)
    (side : relation) :
    {u : unit | 0Z <= S.length (select values pivot side) &&
      S.length (select values pivot side) <= S.length values} =
  select_def values pivot side;
  S.length_def values;
  S.length_def (select values pivot side);
  match values with
  | [] -> ()
  | _ :: tail -> select_length tail pivot side; ()

let rec (select_count @ total) (values : int list) (pivot : int)
    (side : relation) (target : int) :
    {u : unit | P.count (select values pivot side) target =
      (if belongs target pivot side then P.count values target else 0Z)} =
  select_def values pivot side;
  P.count_def values target;
  P.count_def (select values pivot side) target;
  match values with
  | [] -> ()
  | _ :: tail -> select_count tail pivot side target; ()

let rec (partition_lengths @ total) (values : int list) (pivot : int) :
    {u : unit | Bigint.add (S.length (select values pivot Less))
      (Bigint.add (S.length (select values pivot Equal))
        (S.length (select values pivot Greater))) = S.length values} =
  select_def values pivot Less;
  select_def values pivot Equal;
  select_def values pivot Greater;
  S.length_def values;
  S.length_def (select values pivot Less);
  S.length_def (select values pivot Equal);
  S.length_def (select values pivot Greater);
  match values with
  | [] -> ()
  | head :: tail ->
    belongs_def head pivot Less;
    belongs_def head pivot Equal;
    belongs_def head pivot Greater;
    partition_lengths tail pivot;
    ()

let (select_permutation @ total) (before : int list) (after : int list)
    (pivot : int) (side : relation) :
    {u : unit | if P.permutation before after then
      P.permutation (select before pivot side) (select after pivot side) &&
      S.length (select before pivot side) =
        S.length (select after pivot side) else true} @ ghost = ghost_ (
  if P.permutation before after then (
    P.count_extensional (select before pivot side) (select after pivot side)
      (fun target ->
        select_count before pivot side target;
        select_count after pivot side target;
        P.permutation_count before after target);
    P.permutation_length (select before pivot side) (select after pivot side));
  ())

let rec (select_empty @ total) (values : int list) (pivot : int) :
    {u : unit |
      (if P.all values pivot false then select values pivot Less === []
        else true) &&
      (if P.all values pivot true then select values pivot Greater === []
        else true)} =
  select_def values pivot Less; select_def values pivot Greater;
  P.all_def values pivot true; P.all_def values pivot false;
  match values with
  | [] -> ()
  | head :: tail ->
    belongs_def head pivot Less; belongs_def head pivot Greater;
    P.accepts_def head pivot true; P.accepts_def head pivot false;
    select_empty tail pivot;
    ()

let rec (rank_bounds @ total) (values : int list) (index : Bigint.t) :
    {u : unit | if P.sorted values && 0Z <= index && index < S.length values
      then S.length (select values (P.element values index) Less) <= index &&
        S.length (select values (P.element values index) Greater) <=
          Bigint.sub (Bigint.sub (S.length values) 1Z) index else true} =
  S.length_def values;
  P.sorted_def values;
  P.element_at values index;
  S.at_def values index;
  match values with
  | [] -> ()
  | head :: tail ->
    let pivot = P.element values index in
    select_def values pivot Less; select_def values pivot Greater;
    S.length_def (select values pivot Less);
    S.length_def (select values pivot Greater);
    belongs_def head pivot Less; belongs_def head pivot Greater;
    if index = 0Z then (
      select_empty tail pivot;
      select_length tail pivot Greater;
      S.length_def [])
    else (
      let next = Bigint.sub index 1Z in
      rank_bounds tail next;
      S.length_def tail;
      P.element_at tail next;
      P.all_get tail head false next;
      P.accepts_def (P.element tail next) head false)

let (partition_permutation @ total) (values : int list) (pivot : int) :
    {u : unit | P.permutation values
      (S.append (select values pivot Less)
        (S.append (select values pivot Equal) (select values pivot Greater)))}
    @ ghost = ghost_ (
  let left = select values pivot Less in
  let same = select values pivot Equal in
  let right = select values pivot Greater in
  P.count_extensional values (S.append left (S.append same right))
    (fun target ->
      select_count values pivot Less target;
      select_count values pivot Equal target;
      select_count values pivot Greater target;
      belongs_def target pivot Less;
      belongs_def target pivot Equal;
      belongs_def target pivot Greater;
      P.count_append left (S.append same right) target;
      P.count_append same right target))

let rec (partition_bounds @ total) (values : int list) (pivot : int) :
    {u : unit | P.all (select values pivot Less) pivot true &&
      P.all (select values pivot Equal) pivot true &&
      P.all (select values pivot Equal) pivot false &&
      P.all (select values pivot Greater) pivot false &&
      P.sorted (select values pivot Equal)} =
  select_def values pivot Less;
  select_def values pivot Equal;
  select_def values pivot Greater;
  P.all_def (select values pivot Less) pivot true;
  P.all_def (select values pivot Equal) pivot true;
  P.all_def (select values pivot Equal) pivot false;
  P.all_def (select values pivot Greater) pivot false;
  P.sorted_def (select values pivot Equal);
  match values with
  | [] -> ()
  | head :: tail ->
    belongs_def head pivot Less;
    belongs_def head pivot Equal;
    belongs_def head pivot Greater;
    P.accepts_def head pivot true;
    P.accepts_def head pivot false;
    partition_bounds tail pivot;
    ()

type picked = { pivot : int; rest : int list }

let (picked_cons @ total) (head : int) (tail : int list)
    (pivot : int) (rest : int list) :
    {u : unit | if P.permutation tail (pivot :: rest) then
      P.permutation (head :: tail) (pivot :: head :: rest) else true}
    @ ghost = ghost_ (
  if P.permutation tail (pivot :: rest) then
    P.count_extensional (head :: tail) (pivot :: head :: rest) (fun target ->
      P.permutation_count tail (pivot :: rest) target;
      P.count_def (head :: tail) target;
      P.count_def (pivot :: rest) target;
      P.count_def (pivot :: head :: rest) target;
      P.count_def (head :: rest) target);
  ())

let rec (pick @ total) (values : int list) (index : Bigint.t) :
    {r : picked option | match r with
      | None -> values === []
      | Some p -> P.permutation values (p.pivot :: p.rest) &&
        Bigint.add 1Z (S.length p.rest) = S.length values &&
        (if 0Z <= index && index < S.length values then
          S.at values index === Some p.pivot else true)} =
  ghost_ (S.length_def values; S.at_def values index);
  match values with
  | [] -> None
  | head :: tail ->
    if index <= 0Z then (
      ghost_ (P.permutation_refl values);
      Some { pivot = head; rest = tail })
    else (
      let next = Bigint.sub index 1Z in
      match pick tail next with
      | None ->
        ghost_ (S.length_def tail; P.permutation_refl values);
        Some { pivot = head; rest = tail }
      | Some p ->
        ghost_ (picked_cons head tail p.pivot p.rest;
          S.length_def (head :: p.rest));
        Some { pivot = p.pivot; rest = head :: p.rest })

let[@def] join (left : int list) (same : int list) (right : int list)
    (pivot : int) =
  S.append left (pivot :: S.append same right)

let rec (equal_append @ total) (same : int list) (right : int list)
    (pivot : int) :
    {u : unit | if P.all same pivot true && P.all same pivot false &&
      P.sorted right && P.all right pivot false then
      P.sorted (S.append same right) &&
      P.all (S.append same right) pivot false else true} =
  S.append_def same right;
  P.all_def same pivot true; P.all_def same pivot false;
  P.sorted_def (S.append same right);
  P.all_def (S.append same right) pivot false;
  match same with
  | [] -> ()
  | head :: tail ->
    P.accepts_def head pivot true; P.accepts_def head pivot false;
    equal_append tail right pivot;
    ()

let (join_sorted @ total) (left : int list) (same : int list)
    (right : int list) (pivot : int) :
    {u : unit | if P.sorted left && P.sorted right &&
      P.all left pivot true && P.all right pivot false &&
      P.all same pivot true && P.all same pivot false then
      P.sorted (join left same right pivot) else true} =
  join_def left same right pivot;
  equal_append same right pivot;
  P.sorted_glue left pivot (S.append same right);
  ()

let (join_permutation @ total) (values : int list) (pivot : int)
    (left : int list) (right : int list) :
    {u : unit | if P.permutation (select values pivot Less) left &&
      P.permutation (select values pivot Greater) right then
      P.permutation (pivot :: values)
        (join left (select values pivot Equal) right pivot) else true}
    @ ghost = ghost_ (
  if P.permutation (select values pivot Less) left &&
      P.permutation (select values pivot Greater) right then (
    let same = select values pivot Equal in
    join_def left same right pivot;
    P.count_extensional (pivot :: values) (join left same right pivot)
      (fun target ->
        P.permutation_count (select values pivot Less) left target;
        P.permutation_count (select values pivot Greater) right target;
        select_count values pivot Less target;
        select_count values pivot Equal target;
        select_count values pivot Greater target;
        belongs_def target pivot Less;
        belongs_def target pivot Equal;
        belongs_def target pivot Greater;
        P.count_append left (pivot :: S.append same right) target;
        P.count_append same right target;
        P.count_def (pivot :: values) target;
        P.count_def (pivot :: S.append same right) target));
  ())

module Make (C : Vox_real_credits.S) (Compare : sig
  type result = #{ order : int; state : C.token @@ ghost }
  val compare : (left : int) -> (right : int) ->
    (token : {t : C.token | Q.le (Q.of_bigint 1Z) (C.credits t)})
      @ unique total ghost ->
    {r : result |
      (r.#order < 0) = (left < right) &&
      (r.#order = 0) = (left = right) &&
      (r.#order > 0) = (left > right) &&
      C.credits r.#state === Q.sub (C.credits token) (Q.of_bigint 1Z)}
      @ unique @@ total
end) = struct
  type result =
    #{ less : int list @@ aliased;
       same : int list @@ aliased;
       greater : int list @@ aliased;
       state : C.token @@ ghost }

  let rec (partition @ total) (values : int list) (pivot : int)
      (token : {t : C.token | C.credits t === Q.of_bigint (S.length values)}
        @ unique total ghost) :
      {r : result |
        r.#less === select values pivot Less &&
        r.#same === select values pivot Equal &&
        r.#greater === select values pivot Greater &&
        C.credits r.#state === Q.of_bigint 0Z} @ unique =
    ghost_ (
      S.length_def values;
      select_def values pivot Less;
      select_def values pivot Equal;
      select_def values pivot Greater);
    match values with
    | [] -> #{ less = []; same = []; greater = []; state = token }
    | head :: tail ->
      ghost_ (
        S.length_def tail);
      let #{ Compare.order; state } = Compare.compare head pivot token in
      let #{ less; same; greater; state } = partition tail pivot state in
      ghost_ (
        belongs_def head pivot Less;
        belongs_def head pivot Equal;
        belongs_def head pivot Greater);
      if order < 0 then #{ less = head :: less; same; greater; state }
      else if order = 0 then #{ less; same = head :: same; greater; state }
      else #{ less; same; greater = head :: greater; state }
end
