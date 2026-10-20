(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml vox_real.mli";
 prebuilt_modules += " vox_real.ml vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml";
 prebuilt_modules += " vox_sort_cost.mli vox_sort_cost.ml vox_harmonic.ml";
 prebuilt_modules += " vox_quicksort_cost.ml";
 prebuilt_modules += " vox_collision_bound.ml vox_geometric_cost.ml";
 { bytecode; }
 { native; }
*)

module Q = Vox_real
module E = Vox_expectation
module C = Vox_real_credits.Make ()
module H = Vox_harmonic
module S = Vox_sequence
module G = Vox_geometric_cost
module B = Vox_collision_bound
module K = Vox_quicksort_cost
module Alias = Vox_real
module Ascribed : module type of Vox_real = Vox_real
type amount = Q.t

let add = Q.add
let negate = Q.neg
let of_bigint = Q.of_bigint
let partial (x : Q.t) = Q.add x

let () =
  let calls = ref 0 in
  let _ = of_bigint (incr calls; 0Z) in
  assert (!calls = 1)

let (ascribed_arithmetic @ total) () :
    {u : unit | Ascribed.add (Ascribed.of_bigint 1Z)
      (Ascribed.of_bigint 2Z) === Ascribed.of_bigint 3Z}
    @ ghost = ghost_ ()

let (scalar_comparisons @ total) (x : amount) (y : amount) :
    {u : unit | (x = y) = (x === y) &&
      (x < y) = Q.lt x y && (x <= y) = Q.le x y &&
      (compare x y = 0) = (x === y) &&
      (compare x y < 0) = Q.lt x y} @ ghost = ghost_ ()

let two : {n : Q.positive | n = 2Z} = 2Z
let three : {n : Q.positive | n = 3Z} = 3Z
let four : {n : Q.positive | n = 4Z} = 4Z
let six : {n : Q.positive | n = 6Z} = 6Z
let eight : {n : Q.positive | n = 8Z} = 8Z
let ten : {n : Q.positive | n = 10Z} = 10Z
let twelve : {n : Q.positive | n = 12Z} = 12Z

let (exact @ total) () :
    {u : unit | Q.of_fraction 1Z two === Q.of_fraction 2Z four &&
      Q.add (Q.of_fraction 1Z two) (Q.of_fraction 1Z three) ===
        Q.of_fraction 5Z six &&
      Q.sub (Q.of_fraction 1Z three) (Q.of_fraction 1Z two) ===
        Q.neg (Q.of_fraction 1Z six) &&
      Q.lt (Q.of_fraction 1Z three) (Q.of_fraction 1Z two) &&
      not (Q.le (Q.of_fraction 1Z two) (Q.of_fraction 1Z three)) &&
      Alias.add (Q.of_fraction 1Z ten) (Q.of_fraction 2Z ten) ===
        Q.of_fraction 3Z ten} @ ghost = ghost_ ()

let (field_laws @ total) (x : Q.t) (y : Q.t) (z : Q.t) :
    {u : unit | Q.add x y === Q.add y x &&
      Q.add x (Q.add y z) === Q.add (Q.add x y) z &&
      Q.mul x (Q.add y z) === Q.add (Q.mul x y) (Q.mul x z) &&
      Q.add x (Q.neg x) === Q.of_bigint 0Z &&
      Q.sub (Q.add x y) y === x} @ ghost = ghost_ ()

let (division @ total) (x : Q.t)
    (y : {q : Q.t | not (q === Q.of_bigint 0Z)}) :
    {u : unit | Q.div (Q.mul x y) y === x &&
      Q.mul (Q.div x y) y === x} @ ghost = ghost_ ()

let (negative_denominator @ total) () : unit @ ghost = ghost_ (
  let denominator = Q.of_bigint (Bigint.neg 2Z) in
  let quotient = Q.div (Q.of_bigint 1Z) denominator in
  (() : {u : unit | quotient === Q.neg (Q.of_fraction 1Z two)}))

let (density @ total) (x : Q.t) (y : {q : Q.t | Q.lt x q}) :
    {u : unit | Q.lt x (Q.divide (Q.add x y) two) &&
      Q.lt (Q.divide (Q.add x y) two) y} @ ghost = ghost_ ()

let (conversion @ total) (n : Bigint.t) (m : Bigint.t) :
    {u : unit | Q.sub (Q.of_bigint (Bigint.add n 1Z)) (Q.of_bigint n) ===
        Q.of_bigint 1Z &&
      (Q.of_bigint n === Q.of_bigint m) = (n = m) &&
      Q.lt (Q.of_bigint n) (Q.of_bigint m) = (n < m)} @ ghost = ghost_ ()

let (split_merge @ total)
    (amount : {q : Q.t | Q.nonnegative q} @ ghost)
    (token : {t : C.token | Q.le amount (C.credits t)}
      @ unique total ghost) :
    {t : C.token | C.credits t === C.credits token}
      @ unique total ghost =
  let {C.left; right} = C.split amount token in
  C.merge left right

let (uniform_pair @ total) (x : Q.t) (y : Q.t) :
    {u : unit | E.uniform [x; y] === Q.divide (Q.add x y) two}
    @ ghost = ghost_ (
  E.uniform_def [x; y];
  S.length_def [x; y]; S.length_def [y]; S.length_def [];
  Q.sum_def [x; y]; Q.sum_def [y]; Q.sum_def []; ())

let (coin_budget @ total) () :
    {u : unit | Q.add (Q.of_bigint 1Z)
      (E.uniform [Q.of_bigint 0Z; Q.of_bigint 2Z]) === Q.of_bigint 2Z}
    @ ghost = ghost_ (uniform_pair (Q.of_bigint 0Z) (Q.of_bigint 2Z))

let (fractional_budget @ total) () : unit @ ghost = ghost_ (
  let initial = Q.of_fraction 3Z two in
  let half = Q.of_fraction 1Z two in
  let token = C.Budget.create initial in
  let {C.left; right} = C.split half token in
  let spent = C.tick right in
  let remainder = C.merge left spent in
  (() : {u : unit | C.credits remainder === half}))

let (expectation_examples @ total) () : unit @ ghost = ghost_ (
  let zero = Q.of_bigint 0Z in
  let hundred = Q.of_bigint 100Z in
  let half = Q.of_fraction 1Z two in
  let third = Q.of_fraction 1Z three in
  uniform_pair zero hundred;
  let (_ : {u : unit | E.uniform [zero; hundred] === Q.of_bigint 50Z}) =
    () in
  E.uniform_shift [zero; hundred] half;
  S.length_def [zero; hundred]; S.length_def [hundred]; S.length_def [];
  let (_ : {u : unit | E.uniform (E.shift [zero; hundred] half) ===
      Q.of_fraction 101Z two}) = () in
  uniform_pair half third;
  (() : {u : unit | E.uniform [half; third] === Q.of_fraction 5Z twelve}))

let (harmonic_examples @ total) () :
    {u : unit | H.harmonic 3Z === Q.of_fraction 11Z six &&
      H.harmonic 4Z === Q.of_fraction 25Z twelve}
    @ ghost = ghost_ (
  H.harmonic_def 0Z; H.harmonic_def 1Z; H.harmonic_def 2Z;
  H.harmonic_def 3Z; H.harmonic_def 4Z; ())

let (geometric_examples @ total) () :
    {u : unit | G.cost 3Z === Q.of_fraction 7Z four &&
      G.survival 3Z === Q.of_fraction 1Z eight} @ ghost = ghost_ (
  G.power_def 0Z; G.power_def 1Z; G.power_def 2Z; G.power_def 3Z;
  G.cost_def 3Z; G.survival_def 3Z; ())

let (collision_examples @ total) () :
    {u : unit | B.collisions 3Z ten === Q.of_fraction 3Z ten &&
      Q.add (B.collisions 2Z ten) (B.additional 2Z 3Z ten) ===
        Q.of_bigint 1Z} @ ghost = ghost_ (
  B.step 2Z 3Z 10Z; B.compose 0Z 2Z 3Z 10Z;
  B.collisions_def 3Z 10Z; B.additional_def 0Z 3Z 10Z;
  B.collisions_def 2Z 10Z; B.additional_def 0Z 5Z 10Z; ())

let (quicksort_example @ total) () :
    {u : unit | E.uniform (K.child_budgets 3Z) === Q.of_fraction 26Z three}
    @ ghost = ghost_ (
  harmonic_examples ();
  K.uniform_children 3Z; K.expected_children_def 3Z;
  K.average_budget 3Z; K.sum_expression_def 3Z (H.harmonic 3Z); ())

let () =
  ghost_ (exact (); negative_denominator (); coin_budget ();
    fractional_budget (); expectation_examples (); harmonic_examples ();
    geometric_examples (); collision_examples (); quicksort_example ());
  let large = ghost_ (
    Bigint.mul (Bigint.of_int max_int) (Bigint.of_int max_int)) in
  ghost_ (conversion large 0Z);
  ghost_ (G.initial ());
  List.iter (fun n ->
    let n = Bigint.of_int n in
    ghost_ (if n >= 0Z then (
      G.step n; G.bounds n;
      (() : {u : unit | Q.le (G.cost n) (Q.of_bigint 2Z)})));
    ()) [0; 1; 2; 3; 10; 100];
  List.iter (fun n ->
    let n = Bigint.of_int n in
    ghost_ (H.nonnegative n; H.logarithmic_bound n;
      (() : {u : unit | Q.le (H.harmonic n)
        (Q.of_bigint (Bigint.add 1Z (Vox_sort_cost.height n)))}));
    ()) [-1; 0; 1; 2; 3; 4; 7; 8; 9; 15; 16; 17];
  List.iter (fun n ->
    let n = Bigint.of_int n in
    ghost_ (if n >= 0Z then (
      K.nonnegative n; K.logarithmic_bound n;
      K.deposit_funds_next n; K.deposit_bound n; K.sum_budgets n;
      let (_ : {u : unit | Q.add (K.budget n) (K.deposit n) ===
          K.budget (Bigint.add n 1Z) && Q.sum (K.budgets n) ===
          K.sum_expression n (H.harmonic n)}) = () in
      if n > 0Z then (
        K.recurrence n;
        (() : {u : unit | Q.le (Q.add (Q.of_bigint (Bigint.sub n 1Z))
          (E.uniform (K.child_budgets n))) (K.budget n)}))));
    ()) [0; 1; 2; 3; 4; 7; 8]
