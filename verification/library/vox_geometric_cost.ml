module Q = Vox_real

let two : Q.positive = 2Z

let[@def] rec power (n : Bigint.t) =
  if n <= 0Z then 1Z else Bigint.mul 2Z (power (Bigint.sub n 1Z))
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let rec (power_bound @ total) (n : Bigint.t) :
    {u : unit | 0Z < power n && n < power n} =
  power_def n;
  if n <= 0Z then () else power_bound (Bigint.sub n 1Z)
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let[@def] (survival @ total) (n : Bigint.t) = ghost_ (
  power_bound n;
  Q.of_fraction 1Z (power n))

let[@def] (cost @ total) (n : Bigint.t) = ghost_ (
  power_bound n;
  Q.of_fraction (Bigint.mul 2Z (Bigint.sub (power n) 1Z)) (power n))

let (initial @ total) () :
    {u : unit | survival 0Z === Q.of_bigint 1Z &&
      cost 0Z === Q.of_bigint 0Z} @ ghost = ghost_ (
  power_def 0Z; survival_def 0Z; cost_def 0Z)

let (step @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit |
      survival (Bigint.add n 1Z) === Q.divide (survival n) two &&
      cost (Bigint.add n 1Z) ===
        Q.add (Q.of_bigint 1Z) (Q.divide (cost n) two)} @ ghost = ghost_ (
  let next = Bigint.add n 1Z in
  power_bound n;
  power_def next;
  survival_def n; survival_def next;
  cost_def n; cost_def next)

let (bounds @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.nonnegative (cost n) &&
      Q.nonnegative (survival n) && Q.le (cost n) (Q.of_bigint 2Z) &&
      Q.add (cost n) (Q.mul (Q.of_bigint 2Z) (survival n)) ===
        Q.of_bigint 2Z} @ ghost = ghost_ (
  power_bound n;
  survival_def n; cost_def n)

let (limit_bound @ total) (epsilon : Q.t)
    (denominator : {d : Q.positive | Q.le (Q.of_fraction 1Z d) epsilon})
    (n : {n : Bigint.t | Bigint.mul 2Z denominator <= n}) :
    {u : unit | Q.le (survival n) epsilon &&
      Q.le (Q.sub (Q.of_bigint 2Z) (cost n)) epsilon} @ ghost = ghost_ (
  power_bound n;
  survival_def n; cost_def n)
