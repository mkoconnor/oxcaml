module Q = Vox_real
module H = Vox_harmonic
module S = Vox_sequence
module Log = Vox_sort_cost
module E = Vox_expectation

let[@def] (budget @ total) (n : Bigint.t) = ghost_ (
  Q.mul (Q.of_bigint (Bigint.mul 2Z (Bigint.add n 1Z))) (H.harmonic n))

let (nonnegative @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.nonnegative (budget n)} @ ghost = ghost_ (
  budget_def n;
  H.nonnegative n)

let (logarithmic_bound @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.le (budget n)
      (Q.of_bigint (Bigint.mul (Bigint.mul 2Z (Bigint.add n 1Z))
        (Bigint.add 1Z (Log.height n))))} @ ghost = ghost_ (
  budget_def n;
  H.logarithmic_bound n)

let (monotonic @ total) (a : {a : Bigint.t | 0Z <= a})
    (b : {b : Bigint.t | a <= b}) :
    {u : unit | Q.le (budget a) (budget b)} @ ghost = ghost_ (
  H.monotonic a b; H.nonnegative b;
  budget_def a; budget_def b)

let[@def] rec (budgets @ total) (n : Bigint.t) = ghost_ (
  if n <= 0Z then []
  else budget (Bigint.sub n 1Z) :: budgets (Bigint.sub n 1Z))
[@@decreases let n : Bigint.t = n in if n > 0Z then n else 0Z]

let[@def] (sum_expression @ total) (n : Bigint.t) (h : Q.t) = ghost_ (
  Q.add (Q.mul (Q.of_bigint (Bigint.mul n (Bigint.add n 1Z))) h)
    (Q.of_fraction (Bigint.sub 0Z (Bigint.mul n (Bigint.add n 3Z))) 2Z))

let (summation_step @ total) (n : Q.positive) (h : Q.t) :
    {u : unit | Q.add (sum_expression (Bigint.sub n 1Z) h)
      (Q.mul (Q.of_bigint (Bigint.mul 2Z n)) h) ===
      sum_expression n (Q.add h (Q.divide (Q.of_bigint 1Z) n))}
    @ ghost = ghost_ (
  sum_expression_def (Bigint.sub n 1Z) h;
  sum_expression_def n (Q.add h (Q.divide (Q.of_bigint 1Z) n)))

let rec (sum_budgets @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.sum (budgets n) ===
      sum_expression n (H.harmonic n)} @ ghost = ghost_ (
  budgets_def n; Q.sum_def (budgets n);
  if n = 0Z then (
    H.harmonic_def 0Z;
    sum_expression_def 0Z (H.harmonic 0Z))
  else (
    let previous = Bigint.sub n 1Z in
    sum_budgets previous;
    budget_def previous; H.harmonic_def n;
    summation_step n (H.harmonic previous)))
[@@decreases n]

let rec (budgets_length @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | S.length (budgets n) = n} @ ghost = ghost_ (
  budgets_def n;
  S.length_def (budgets n);
  if n = 0Z then () else budgets_length (Bigint.sub n 1Z))
[@@decreases n]

let (average_budget @ total) (n : Q.positive) :
    {u : unit | E.uniform (budgets n) ===
      Q.divide (sum_expression n (H.harmonic n)) n} @ ghost = ghost_ (
  budgets_length n;
  budgets_def n;
  E.uniform_def (budgets n);
  sum_budgets n)

let[@def] (expected_children @ total) (n : Bigint.t) = ghost_ (
  Q.mul (Q.of_bigint 2Z) (E.uniform (budgets n)))

let[@def] (child_budgets @ total) (n : Bigint.t) = ghost_ (
  E.pairwise_add (budgets n) (E.reverse (budgets n)))

let (uniform_children @ total) (n : Bigint.t) :
    {u : unit | E.uniform (child_budgets n) === expected_children n}
    @ ghost = ghost_ (
  child_budgets_def n; expected_children_def n;
  E.reverse_length (budgets n);
  E.uniform_reverse (budgets n);
  E.uniform_pairwise (budgets n) (E.reverse (budgets n)))

let rec (budgets_at @ total) (n : {n : Bigint.t | 0Z <= n})
    (index : Bigint.t) :
    {u : unit | if 0Z <= index && index < n then
      S.at (budgets n) index ===
        Some (budget (Bigint.sub (Bigint.sub n 1Z) index)) else true}
    @ ghost = ghost_ (
  budgets_def n; S.at_def (budgets n) index;
  if n > 0Z then budgets_at (Bigint.sub n 1Z) (Bigint.sub index 1Z);
  ())
[@@decreases n]

let (children_at @ total) (n : {n : Bigint.t | 0Z <= n})
    (index : Bigint.t) :
    {u : unit | S.length (child_budgets n) = n &&
      (if 0Z <= index && index < n then S.at (child_budgets n) index ===
        Some (Q.add (budget (Bigint.sub (Bigint.sub n 1Z) index))
          (budget index)) else true)} @ ghost = ghost_ (
  child_budgets_def n;
  budgets_length n;
  E.reverse_length (budgets n);
  E.pairwise_sum (budgets n) (E.reverse (budgets n));
  E.pairwise_at (budgets n) (E.reverse (budgets n)) index;
  E.reverse_at (budgets n) index;
  budgets_at n index;
  budgets_at n (Bigint.sub (Bigint.sub n 1Z) index))

let (recurrence_formula @ total) (n : Q.positive) (h : Q.t) :
    {u : unit | Q.add (Q.of_bigint (Bigint.sub n 1Z))
      (Q.mul (Q.of_bigint 2Z) (Q.divide (sum_expression n h) n)) ===
      Q.sub (Q.mul (Q.of_bigint (Bigint.mul 2Z (Bigint.add n 1Z))) h)
        (Q.of_bigint 4Z)} @ ghost = ghost_ (
  sum_expression_def n h)

let (recurrence @ total) (n : Q.positive) :
    {u : unit | Q.le
      (Q.add (Q.of_bigint (Bigint.sub n 1Z)) (E.uniform (child_budgets n)))
      (budget n)} @ ghost = ghost_ (
  expected_children_def n; budget_def n;
  average_budget n;
  recurrence_formula n (H.harmonic n);
  uniform_children n)

let[@def] (deposit @ total) (n : Bigint.t) = ghost_ (
  Q.sub (budget (Bigint.add n 1Z)) (budget n))

let (deposit_funds_next @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.nonnegative (deposit n) &&
      Q.add (budget n) (deposit n) === budget (Bigint.add n 1Z)}
    @ ghost = ghost_ (
  deposit_def n;
  monotonic n (Bigint.add n 1Z))

let (deposit_formula @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | deposit n ===
      Q.add (Q.mul (Q.of_bigint 2Z) (H.harmonic (Bigint.add n 1Z)))
        (Q.of_bigint 2Z)} @ ghost = ghost_ (
  let next = Bigint.add n 1Z in
  deposit_def n; budget_def n; budget_def next;
  H.harmonic_def next)

let (deposit_bound @ total) (n : {n : Bigint.t | 0Z <= n}) :
    {u : unit | Q.le (deposit n)
      (Q.of_bigint (Bigint.mul 2Z (Bigint.add 2Z
        (Log.height (Bigint.add n 1Z)))))} @ ghost = ghost_ (
  let next = Bigint.add n 1Z in
  deposit_formula n;
  H.logarithmic_bound next)
