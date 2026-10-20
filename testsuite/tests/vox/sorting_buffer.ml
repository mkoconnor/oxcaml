(* TEST
 has-z3;
 flags = "-extension refinement_types -principal -vox-probabilistic";
 use_runtime = "false";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_int_sequence.mli vox_int_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_quicksort_partition.ml";
 prebuilt_modules += " vox_sort_cost.mli vox_sort_cost.ml";
 prebuilt_modules += " vox_expectation.ml vox_harmonic.ml";
 prebuilt_modules += " vox_quicksort_cost.ml vox_quicksort_average.ml";
 prebuilt_modules += " vox_probability.mli vox_probability.ml";
 prebuilt_modules += " vox_randomized_quicksort.mli";
 prebuilt_modules += " vox_randomized_quicksort.ml";
 prebuilt_modules += " vox_sorting_buffer.mli vox_sorting_buffer.ml";
 { bytecode; }
 { native; }
*)

module Buffer = Vox_sorting_buffer
module Q = Vox_real
module S = Vox_sequence
module B = Vox_quicksort_cost
module P = Vox_probability
module C = P.Cost

let[@def] rec fees (n : Bigint.t) (values : int list) = ghost_ (
  match values with
  | [] -> Q.of_bigint 0Z
  | _ :: rest -> Q.add (B.deposit n) (fees (Bigint.add n 1Z) rest))

let rec (fees_nonnegative @ total)
    (n : {n : Bigint.t | 0Z <= n}) (values : int list) :
    {u : unit | Q.nonnegative (fees n values)} @ ghost = ghost_ (
  fees_def n values;
  match values with
  | [] -> ()
  | _ :: rest ->
    B.deposit_funds_next n;
    fees_nonnegative (Bigint.add n 1Z) rest)

let rec fill (values : int list)
    (buffer : {b : Buffer.t | Buffer.valid b &&
      Bigint.add (S.length (Buffer.contents b)) (S.length values) <=
        Bigint.of_int max_int} @ unique)
    (cost : {t : C.token | Q.le
      (fees (S.length (Buffer.contents buffer)) values) (C.credits t)}
      @ unique total ghost) :
    {b : Buffer.t | Buffer.valid b} @ unique =
  ghost_ (S.length_def values);
  match values with
  | [] -> buffer
  | value :: rest ->
    let n = ghost_ (S.length (Buffer.contents (borrow_ buffer))) in
    ghost_ (
      S.length_def (Buffer.contents (borrow_ buffer));
      S.length_def rest; fees_def n values;
      Buffer.fee_law (borrow_ buffer);
      fees_nonnegative (Bigint.add n 1Z) rest);
    let #{Buffer.buffer; cost} = Buffer.push value buffer cost in
    ghost_ (S.length_def (Buffer.contents (borrow_ buffer)));
    fill rest buffer cost

let[@def] rec budget (cases : int list list) = ghost_ (
  match cases with
  | [] -> Q.of_bigint 0Z
  | values :: rest -> Q.add (fees 0Z values) (budget rest))

let rec (nonnegative @ total) (cases : int list list) :
    {u : unit | Q.nonnegative (budget cases)} @ ghost = ghost_ (
  budget_def cases;
  match cases with
  | [] -> ()
  | values :: rest ->
    fees_nonnegative 0Z values; nonnegative rest)

let rec check : (cases : int list list) ->
    {t : C.token | Q.le (budget cases) (C.credits t)}
      @ unique total ghost -> unit = fun cases cost ->
  ghost_ (budget_def cases);
  match cases with
  | [] -> ()
  | values :: rest ->
    let amount = ghost_ (fees 0Z values) in
    ghost_ (
      fees_nonnegative 0Z values; nonnegative rest);
    let {C.left; right} = C.split amount cost in
    if S.length values <= Bigint.of_int max_int then (
      let buffer = Buffer.empty () in
      ghost_ (S.length_def []);
      let buffer = fill values buffer left in
      ghost_ (Buffer.potential_law (borrow_ buffer));
      assert (Buffer.drain buffer = List.sort Stdlib.compare values));
    check rest right

let () =
  let cases =
    [[]; [1]; [2; 1]; [3; 1; 2; 3; 2; 1];
     [min_int; max_int; 0]; List.init 30 (fun i -> i mod 5)] in
  let cases = List.concat (List.init 10 (fun _ -> cases)) in
  let amount = ghost_ (budget cases) in
  let zero = ghost_ (Q.of_bigint 0Z) in
  ghost_ (nonnegative cases);
  P.run amount zero (fun cost _error _monitor -> check cases cost)
