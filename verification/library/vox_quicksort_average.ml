module Q = Vox_real
module E = Vox_expectation
module S = Vox_sequence
module P = Vox_int_sequence
module C = Vox_quicksort_cost
module Part = Vox_quicksort_partition

let[@def] (children @ total) (values : int list) (pivot : int) = ghost_ (
  Q.add (C.budget (S.length (Part.select values pivot Part.Less)))
    (C.budget (S.length (Part.select values pivot Part.Greater))))

let[@def] rec (allocations @ total) (values : int list)
    (pivots : int list) = ghost_ (
  match pivots with
  | [] -> []
  | pivot :: tail -> children values pivot :: allocations values tail)

let (children_nonnegative @ total) (values : int list) (pivot : int) :
    {u : unit | Q.nonnegative (children values pivot)}
    @ ghost = ghost_ (
  children_def values pivot;
  Part.select_length values pivot Part.Less;
  Part.select_length values pivot Part.Greater;
  C.nonnegative (S.length (Part.select values pivot Part.Less));
  C.nonnegative (S.length (Part.select values pivot Part.Greater)))

let rec (allocations_nonnegative @ total) (values : int list)
    (pivots : int list) :
    {u : unit | Q.all_nonnegative (allocations values pivots)}
    @ ghost = ghost_ (
  allocations_def values pivots;
  Q.all_nonnegative_def (allocations values pivots);
  match pivots with
  | [] -> ()
  | pivot :: tail ->
    children_nonnegative values pivot;
    allocations_nonnegative values tail)

let (picked_children @ total) (values : int list) (pivot : int)
    (rest : int list) :
    {u : unit | if P.permutation values (pivot :: rest) then
      children values pivot === children rest pivot else true}
    @ ghost = ghost_ (
  Part.select_permutation values (pivot :: rest) pivot Part.Less;
  Part.select_permutation values (pivot :: rest) pivot Part.Greater;
  Part.select_def (pivot :: rest) pivot Part.Less;
  Part.select_def (pivot :: rest) pivot Part.Greater;
  Part.belongs_def pivot pivot Part.Less;
  Part.belongs_def pivot pivot Part.Greater;
  children_def values pivot; children_def rest pivot)

let rec (allocations_length @ total) (values : int list) (pivots : int list) :
    {u : unit | S.length (allocations values pivots) = S.length pivots}
    @ ghost = ghost_ (
  allocations_def values pivots;
  S.length_def pivots; S.length_def (allocations values pivots);
  match pivots with
  | [] -> ()
  | _ :: tail -> allocations_length values tail)

let rec (allocations_at @ total) (values : int list) (pivots : int list)
    (index : Bigint.t) :
    {u : unit | S.at (allocations values pivots) index ===
      (match S.at pivots index with
      | None -> None | Some pivot -> Some (children values pivot))}
    @ ghost = ghost_ (
  allocations_def values pivots;
  S.at_def pivots index; S.at_def (allocations values pivots) index;
  match pivots with
  | [] -> ()
  | _ :: tail -> allocations_at values tail (Bigint.sub index 1Z))

let rec (sum_insert @ total) (values : int list) (pivot : int)
    (pivots : int list) :
    {u : unit | Q.sum (allocations values (P.insert pivot pivots)) ===
      Q.add (children values pivot) (Q.sum (allocations values pivots))}
    @ ghost = ghost_ (
  P.insert_def pivot pivots;
  allocations_def values pivots;
  allocations_def values (P.insert pivot pivots);
  Q.sum_def (allocations values pivots);
  Q.sum_def (allocations values (P.insert pivot pivots));
  match pivots with
  | [] -> ()
  | head :: tail ->
    if pivot > head then sum_insert values pivot tail;
    ())

let rec (sum_sorted @ total) (values : int list) (pivots : int list) :
    {u : unit | Q.sum (allocations values (P.sorted_copy pivots)) ===
      Q.sum (allocations values pivots)}
    @ ghost = ghost_ (
  P.sorted_copy_unfold pivots;
  allocations_def values pivots;
  Q.sum_def (allocations values pivots);
  match pivots with
  | [] -> ()
  | pivot :: tail ->
    sum_sorted values tail;
    sum_insert values pivot (P.sorted_copy tail))

let (uniform_sorted @ total) (values : int list) (pivots : int list) :
    {u : unit | E.uniform (allocations values (P.sorted_copy pivots)) ===
      E.uniform (allocations values pivots)}
    @ ghost = ghost_ (
  let sorted = P.sorted_copy pivots in
  allocations_length values pivots;
  allocations_length values sorted;
  sum_sorted values pivots;
  let before = allocations values pivots in
  let after = allocations values sorted in
  E.uniform_def before; E.uniform_def after;
  S.length_def before; S.length_def after;
  match before, after with
  | [], [] -> ()
  | _ :: _, _ :: _ -> ())

let (rank_bound @ total) (values : int list) (sorted : int list)
    (index : Bigint.t) :
    {u : unit | if P.permutation values sorted && P.sorted sorted &&
      0Z <= index && index < S.length sorted then
      Q.le (children values (P.element sorted index))
        (Q.add (C.budget (Bigint.sub (Bigint.sub (S.length sorted) 1Z) index))
          (C.budget index)) else true}
    @ ghost = ghost_ (
  if P.permutation values sorted && P.sorted sorted &&
      0Z <= index && index < S.length sorted then (
    let pivot = P.element sorted index in
    let low = S.length (Part.select values pivot Part.Less) in
    let high = S.length (Part.select values pivot Part.Greater) in
    let other = Bigint.sub (Bigint.sub (S.length sorted) 1Z) index in
    Part.rank_bounds sorted index;
    Part.select_permutation values sorted pivot Part.Less;
    Part.select_permutation values sorted pivot Part.Greater;
    Part.select_length values pivot Part.Less;
    Part.select_length values pivot Part.Greater;
    C.monotonic low index; C.monotonic high other;
    children_def values pivot);
  ())

let (pointwise_bound @ total) (values : int list) (sorted : int list) :
    {u : unit | if P.permutation values sorted && P.sorted sorted then
      E.pointwise_le (allocations values sorted)
        (C.child_budgets (S.length sorted)) else true}
    @ ghost = ghost_ (
  if P.permutation values sorted && P.sorted sorted then (
    S.length_def sorted;
    let n = S.length sorted in
    allocations_length values sorted;
    E.pointwise_intro (allocations values sorted) (C.child_budgets n)
      (fun index ->
        C.children_at n index;
        allocations_at values sorted index;
        P.element_at sorted index;
        S.at_outside sorted index;
        rank_bound values sorted index));
  ())

let (average_bound @ total) (values : int list) :
    {u : unit | if 0Z < S.length values then
      Q.le (Q.add (Q.of_bigint (Bigint.sub (S.length values) 1Z))
        (E.uniform (allocations values values))) (C.budget (S.length values))
      else true}
    @ ghost = ghost_ (
  if 0Z < S.length values then (
    let sorted = P.sorted_copy values in
    let n = S.length values in
    pointwise_bound values sorted;
    E.uniform_le (allocations values sorted) (C.child_budgets n);
    uniform_sorted values values;
    C.recurrence n);
  ())

let (remaining_bound @ total) (values : int list) :
    {u : unit | if 0Z < S.length values then
      Q.le (E.uniform (allocations values values))
        (Q.sub (C.budget (S.length values))
          (Q.of_bigint (Bigint.sub (S.length values) 1Z)))
      else true}
    @ ghost = ghost_ (
  average_bound values)
