module Q = Vox_real

let[@def] (additional @ total) (seen : Bigint.t) (draws : Bigint.t)
    (size : Q.positive) = ghost_ (
  Q.of_fraction
    (Bigint.mul draws
      (Bigint.sub (Bigint.add (Bigint.mul 2Z seen) draws) 1Z))
    (Bigint.mul 2Z size))

let[@def] (collisions @ total) (draws : Bigint.t) (size : Q.positive) =
  ghost_ (additional 0Z draws size)

let (nonnegative @ total) (seen : {n : Bigint.t | 0Z <= n})
    (draws : {n : Bigint.t | 0Z <= n}) (size : Q.positive) :
    {u : unit | Q.nonnegative (additional seen draws size)}
    @ ghost = ghost_ (
  additional_def seen draws size)

let (empty @ total) (seen : Bigint.t) (size : Q.positive) :
    {u : unit | additional seen 0Z size === Q.of_bigint 0Z}
    @ ghost = ghost_ (
  additional_def seen 0Z size)

let (one @ total) (seen : Bigint.t) (size : Q.positive) :
    {u : unit | additional seen 1Z size ===
      Q.divide (Q.of_bigint seen) size} @ ghost = ghost_ (
  additional_def seen 1Z size)

let (compose @ total) (seen : Bigint.t) (first : Bigint.t)
    (second : Bigint.t) (size : Q.positive) :
    {u : unit | Q.add (additional seen first size)
      (additional (Bigint.add seen first) second size) ===
      additional seen (Bigint.add first second) size} @ ghost = ghost_ (
  additional_def seen first size;
  additional_def (Bigint.add seen first) second size;
  additional_def seen (Bigint.add first second) size)

let (step @ total) (seen : Bigint.t)
    (draws : {n : Bigint.t | 0Z < n}) (size : Q.positive) :
    {u : unit | Q.add (Q.divide (Q.of_bigint seen) size)
      (additional (Bigint.add seen 1Z) (Bigint.sub draws 1Z) size) ===
      additional seen draws size} @ ghost = ghost_ (
  one seen size;
  compose seen 1Z (Bigint.sub draws 1Z) size)
