type t : logical_data

external of_bigint : Bigint.t -> t @ ghost @@ total =
  "caml_vox_real_of_bigint"
external neg : t -> t @ ghost @@ total = "caml_vox_real_neg"
external add : t -> t -> t @ ghost @@ total = "caml_vox_real_add"
external sub : t -> t -> t @ ghost @@ total = "caml_vox_real_sub"
external mul : t -> t -> t @ ghost @@ total = "caml_vox_real_mul"
external div : t -> {y : t | not (y === of_bigint 0Z)} -> t @ ghost
  @@ total = "caml_vox_real_div"
external le : t -> t -> bool @ ghost @@ total = "caml_vox_real_le"
external lt : t -> t -> bool @ ghost @@ total = "caml_vox_real_lt"

type positive = {n : Bigint.t | n > 0Z}

let[@def transparent] (of_positive @ total) (n : positive) :
    {q : t | not (q === of_bigint 0Z)} @ ghost =
  ghost_ (of_bigint n)

let[@def transparent] (of_fraction @ total)
    (n : Bigint.t) (d : positive) : t @ ghost =
  ghost_ (div (of_bigint n) (of_positive d))

let[@def transparent] (divide @ total) (x : t) (n : positive) : t @ ghost =
  ghost_ (div x (of_positive n))

let[@def transparent] (nonnegative @ total) (x : t) : bool @ ghost =
  ghost_ (le (of_bigint 0Z) x)

let[@def] rec (sum @ total) (values : t list) : t @ ghost = ghost_ (
  match values with
  | [] -> of_bigint 0Z
  | head :: tail -> add head (sum tail))

let[@def] rec (all_nonnegative @ total) (values : t list) : bool @ ghost =
  ghost_ (match values with
  | [] -> true
  | head :: tail -> nonnegative head && all_nonnegative tail)

let rec (sum_nonnegative @ total) (values : t list) :
    {u : unit | if all_nonnegative values then
      nonnegative (sum values) else true} @ ghost = ghost_ (
  all_nonnegative_def values; sum_def values;
  match values with
  | [] -> ()
  | _ :: tail -> sum_nonnegative tail)
