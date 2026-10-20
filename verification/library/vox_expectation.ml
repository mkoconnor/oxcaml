module Q = Vox_real
module S = Vox_sequence

let[@def] uniform (values : Q.t list) = ghost_ (
  S.length_def values;
  match values with
  | [] -> Q.of_bigint 0Z
  | _ :: _ -> Q.divide (Q.sum values) (S.length values))

let[@def] entry (values : Q.t list) (index : Bigint.t) = ghost_ (
  match S.at values index with
  | None -> Q.of_bigint 0Z
  | Some value -> value)

let rec (entry_nonnegative @ total) (values : Q.t list) (index : Bigint.t) :
    {u : unit | if Q.all_nonnegative values then
      Q.nonnegative (entry values index) else true} @ ghost = ghost_ (
  Q.all_nonnegative_def values;
  entry_def values index;
  S.at_def values index;
  match values with
  | [] -> ()
  | _ :: tail ->
    entry_nonnegative tail (Bigint.sub index 1Z);
    entry_def tail (Bigint.sub index 1Z))

let (uniform_nonnegative @ total) (values : Q.t list) :
    {u : unit | if Q.all_nonnegative values then
      Q.nonnegative (uniform values) else true} @ ghost = ghost_ (
  uniform_def values;
  S.length_def values;
  Q.sum_nonnegative values)

let[@def] rec pointwise_le (left : Q.t list) (right : Q.t list) = ghost_ (
  match left, right with
  | [], [] -> true
  | x :: xs, y :: ys -> Q.le x y && pointwise_le xs ys
  | _ -> false)

let rec (sum_le @ total) (left : Q.t list) (right : Q.t list) :
    {u : unit | if pointwise_le left right then
      S.length left = S.length right && Q.le (Q.sum left) (Q.sum right)
      else true} @ ghost = ghost_ (
  pointwise_le_def left right;
  Q.sum_def left; Q.sum_def right;
  S.length_def left; S.length_def right;
  match left, right with
  | _ :: xs, _ :: ys -> sum_le xs ys; ()
  | _ -> ())

let (uniform_le @ total) (left : Q.t list) (right : Q.t list) :
    {u : unit | if pointwise_le left right then
      Q.le (uniform left) (uniform right) else true} @ ghost = ghost_ (
  pointwise_le_def left right;
  uniform_def left; uniform_def right;
  S.length_def left; S.length_def right;
  sum_le left right)

let[@def] rec shift (values : Q.t list) (reserve : Q.t) = ghost_ (
  match values with
  | [] -> []
  | head :: tail -> Q.add head reserve :: shift tail reserve)

let rec (shift_length @ total) (values : Q.t list) (reserve : Q.t) :
    {u : unit | S.length (shift values reserve) = S.length values}
    @ ghost = ghost_ (
  shift_def values reserve;
  S.length_def values;
  S.length_def (shift values reserve);
  match values with
  | [] -> ()
  | _ :: tail -> shift_length tail reserve)

let rec (sum_shift @ total) (values : Q.t list) (reserve : Q.t) :
    {u : unit | Q.sum (shift values reserve) ===
      Q.add (Q.sum values) (Q.mul (Q.of_bigint (S.length values)) reserve)}
    @ ghost = ghost_ (
  shift_def values reserve;
  Q.sum_def values; Q.sum_def (shift values reserve);
  S.length_def values;
  match values with
  | [] -> ()
  | _ :: tail -> sum_shift tail reserve)

let (uniform_shift @ total) (values : Q.t list) (reserve : Q.t) :
    {u : unit | if S.length values > 0Z then
      uniform (shift values reserve) === Q.add (uniform values) reserve
      else true} @ ghost = ghost_ (
  S.length_def values;
  shift_def values reserve;
  shift_length values reserve;
  uniform_def values; uniform_def (shift values reserve);
  sum_shift values reserve)

let rec (sum_append @ total) (left : Q.t list) (right : Q.t list) :
    {u : unit | Q.sum (S.append left right) ===
      Q.add (Q.sum left) (Q.sum right)} @ ghost = ghost_ (
  S.append_def left right;
  Q.sum_def left; Q.sum_def (S.append left right);
  match left with
  | [] -> ()
  | _ :: tail -> sum_append tail right)

let[@def] rec reverse (values : Q.t list) = ghost_ (
  match values with
  | [] -> []
  | head :: tail -> S.append (reverse tail) [head])

let rec (reverse_length @ total) (values : Q.t list) :
    {u : unit | S.length (reverse values) = S.length values} @ ghost = ghost_ (
  reverse_def values;
  S.length_def values; S.length_def (reverse values);
  match values with
  | [] -> ()
  | head :: tail ->
    reverse_length tail;
    S.append_length (reverse tail) [head];
    S.length_def [head]; S.length_def [])

let rec (sum_reverse @ total) (values : Q.t list) :
    {u : unit | Q.sum (reverse values) === Q.sum values} @ ghost = ghost_ (
  reverse_def values;
  Q.sum_def values; Q.sum_def (reverse values);
  match values with
  | [] -> ()
  | head :: tail ->
    sum_reverse tail;
    sum_append (reverse tail) [head];
    Q.sum_def [head]; Q.sum_def [])

let (uniform_reverse @ total) (values : Q.t list) :
    {u : unit | uniform (reverse values) === uniform values}
    @ ghost = ghost_ (
  reverse_length values; sum_reverse values;
  uniform_def values; uniform_def (reverse values);
  S.length_def values; S.length_def (reverse values))

let[@def] rec pairwise_add (left : Q.t list) (right : Q.t list) = ghost_ (
  match left, right with
  | x :: xs, y :: ys -> Q.add x y :: pairwise_add xs ys
  | _ -> [])

let rec (pairwise_sum @ total) (left : Q.t list) (right : Q.t list) :
    {u : unit | if S.length left = S.length right then
      S.length (pairwise_add left right) = S.length left &&
      Q.sum (pairwise_add left right) === Q.add (Q.sum left) (Q.sum right)
      else true} @ ghost = ghost_ (
  pairwise_add_def left right;
  S.length_def left; S.length_def right;
  S.length_def (pairwise_add left right);
  Q.sum_def left; Q.sum_def right;
  Q.sum_def (pairwise_add left right);
  match left, right with
  | _ :: xs, _ :: ys -> pairwise_sum xs ys; ()
  | _ -> ())

let (uniform_pairwise @ total) (left : Q.t list) (right : Q.t list) :
    {u : unit | if S.length left = S.length right then
      uniform (pairwise_add left right) ===
        Q.add (uniform left) (uniform right) else true} @ ghost = ghost_ (
  pairwise_sum left right;
  pairwise_add_def left right;
  uniform_def left; uniform_def right;
  uniform_def (pairwise_add left right);
  S.length_def left; S.length_def right)

let rec (append_at @ total) (left : Q.t list) (right : Q.t list)
    (index : Bigint.t) :
    {u : unit | if 0Z <= index then
      S.at (S.append left right) index ===
        (if index < S.length left then S.at left index
          else S.at right (Bigint.sub index (S.length left))) else true}
    @ ghost = ghost_ (
  S.append_def left right; S.length_def left;
  S.at_def left index; S.at_def (S.append left right) index;
  match left with
  | [] -> ()
  | _ :: tail ->
    S.length_def tail;
    if index > 0Z then append_at tail right (Bigint.sub index 1Z);
    ())

let rec (reverse_at @ total) (values : Q.t list) (index : Bigint.t) :
    {u : unit | if 0Z <= index && index < S.length values then
      S.at (reverse values) index ===
        S.at values (Bigint.sub (Bigint.sub (S.length values) 1Z) index)
      else true} @ ghost = ghost_ (
  reverse_def values; S.length_def values;
  match values with
  | [] -> ()
  | head :: tail ->
    reverse_length tail;
    S.length_def tail;
    append_at (reverse tail) [head] index;
    reverse_at tail index;
    S.at_def [head] (Bigint.sub index (S.length tail));
    S.at_def values (Bigint.sub (Bigint.sub (S.length values) 1Z) index))

let rec (pairwise_at @ total) (left : Q.t list) (right : Q.t list)
    (index : Bigint.t) :
    {u : unit | if 0Z <= index && S.length left = S.length right then
      S.at (pairwise_add left right) index ===
        (match S.at left index, S.at right index with
        | Some x, Some y -> Some (Q.add x y) | _ -> None) else true}
    @ ghost = ghost_ (
  pairwise_add_def left right;
  S.length_def left; S.length_def right;
  S.at_def left index; S.at_def right index;
  S.at_def (pairwise_add left right) index;
  match left, right with
  | _ :: xs, _ :: ys ->
    if index > 0Z then pairwise_at xs ys (Bigint.sub index 1Z);
    ()
  | _ -> ())

let rec (pointwise_intro @ total) (left : Q.t list) (right : Q.t list)
    (proof : ((index : Bigint.t) ->
      {u : unit | S.length left = S.length right &&
        (if 0Z <= index then match S.at left index, S.at right index with
          | Some x, Some y -> Q.le x y | _ -> true else true)}
        @ ghost) @ total) :
    {u : unit | pointwise_le left right} @ ghost = ghost_ (
  proof 0Z;
  pointwise_le_def left right;
  S.length_def left; S.length_def right;
  S.at_def left 0Z; S.at_def right 0Z;
  match left, right with
  | _ :: xs, _ :: ys ->
    pointwise_intro xs ys (fun index ->
      proof (Bigint.add index 1Z);
      S.at_def left (Bigint.add index 1Z);
      S.at_def right (Bigint.add index 1Z));
    ()
  | _ -> ())

let[@def] rec zeros (n : Bigint.t) = ghost_ (
  if n <= 0Z then [] else Q.of_bigint 0Z :: zeros (Bigint.sub n 1Z))
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let rec (zeros_facts @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | S.length (zeros n) = n && Q.all_nonnegative (zeros n) &&
      Q.sum (zeros n) === Q.of_bigint 0Z} @ ghost = ghost_ (
  zeros_def n; S.length_def (zeros n);
  Q.all_nonnegative_def (zeros n); Q.sum_def (zeros n);
  if n > 0Z then zeros_facts (Bigint.sub n 1Z);
  ())
[@@decreases n]

let (zeros_mean @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | uniform (zeros n) === Q.of_bigint 0Z} @ ghost = ghost_ (
  zeros_facts n;
  zeros_def n; uniform_def (zeros n))

let[@def] pair_mean (left : Q.t) (right : Q.t) = ghost_ (
  Q.divide (Q.add left right) 2Z)

let (uniform_pair @ total) (left : Q.t) (right : Q.t) :
    {u : unit | uniform [left; right] === pair_mean left right}
    @ ghost = ghost_ (
  uniform_def [left; right];
  S.length_def [left; right]; S.length_def [right]; S.length_def [];
  Q.sum_def [left; right]; Q.sum_def [right]; Q.sum_def [];
  pair_mean_def left right)
