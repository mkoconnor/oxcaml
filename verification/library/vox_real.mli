@@ portable

(** Exact mathematical real numbers. Numeric operations are ghost. *)
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

val of_positive : positive -> {q : t | not (q === of_bigint 0Z)}
  @ ghost @@ total [@@def transparent]
val of_positive_def : (n : positive) ->
  {u : unit | of_positive n === of_bigint n} @@ total

val of_fraction : Bigint.t -> positive -> t @ ghost @@ total
  [@@def transparent]
val of_fraction_def : (n : Bigint.t) -> (d : positive) ->
  {u : unit | of_fraction n d === div (of_bigint n) (of_positive d)}
  @@ total

val divide : t -> positive -> t @ ghost @@ total [@@def transparent]
val divide_def : (x : t) -> (n : positive) ->
  {u : unit | divide x n === div x (of_positive n)} @@ total

val nonnegative : t -> bool @ ghost @@ total [@@def transparent]
val nonnegative_def : (x : t) ->
  {u : unit | nonnegative x === le (of_bigint 0Z) x} @@ total

val sum : t list -> t @ ghost @@ total

val sum_def : (values : t list) ->
  {u : unit | sum values === (match values with
    | [] -> of_bigint 0Z
    | head :: tail -> add head (sum tail))} @@ total

val all_nonnegative : t list -> bool @ ghost @@ total

val all_nonnegative_def : (values : t list) ->
  {u : unit | all_nonnegative values = (match values with
    | [] -> true
    | head :: tail -> nonnegative head && all_nonnegative tail)} @@ total

val sum_nonnegative : (values : t list) ->
  {u : unit | if all_nonnegative values then
    nonnegative (sum values) else true} @ ghost @@ total
