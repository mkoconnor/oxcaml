module Q = Vox_real
module Log = Vox_sort_cost

let[@def] rec (harmonic @ total) (n : Bigint.t) = ghost_ (
  if n <= 0Z then Q.of_bigint 0Z
  else Q.add (harmonic (Bigint.sub n 1Z)) (Q.divide (Q.of_bigint 1Z) n))
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let rec (monotonic @ total) (a : {a : Bigint.t | 0Z <= a})
    (b : {b : Bigint.t | a <= b}) :
    {u : unit | Q.le (harmonic a) (harmonic b)} @ ghost = ghost_ (
  if a < b then (
    monotonic a (Bigint.sub b 1Z);
    harmonic_def b);
  ())
[@@decreases Bigint.sub b a]

let rec (nonnegative @ total) (n : Bigint.t) :
    {u : unit | Q.nonnegative (harmonic n)} @ ghost = ghost_ (
  harmonic_def n;
  if n > 0Z then nonnegative (Bigint.sub n 1Z);
  ())
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let (extend_tail @ total) (base : Q.t) (a : Q.positive)
    (b : Q.positive) :
    {u : unit | if a < b then Q.le
      (Q.add (Q.add base (Q.divide (Q.of_bigint (Bigint.sub
        (Bigint.sub b a) 1Z)) a)) (Q.divide (Q.of_bigint 1Z) b))
      (Q.add base (Q.divide (Q.of_bigint (Bigint.sub b a)) a))
      else true} @ ghost = ghost_ (
  ())

let rec (tail_bound @ total) (a : Q.positive)
    (b : {b : Bigint.t | a <= b}) :
    {u : unit | Q.le (harmonic b)
      (Q.add (harmonic a) (Q.divide (Q.of_bigint (Bigint.sub b a)) a))}
    @ ghost = ghost_ (
  if a = b then ()
  else (
    tail_bound a (Bigint.sub b 1Z);
    harmonic_def b;
    extend_tail (harmonic a) a b))
[@@decreases Bigint.sub b a]

let rec (logarithmic_bound @ total) (n : Bigint.t) :
    {u : unit | Q.le (harmonic n)
      (Q.of_bigint (Bigint.add 1Z (Log.height n)))} @ ghost = ghost_ (
  Log.height_def n;
  if n <= 1Z then (
    harmonic_def n;
    harmonic_def 0Z)
  else (
    let half = Bigint.div (Bigint.add n 1Z) 2Z in
    logarithmic_bound half;
    tail_bound half n))
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]
