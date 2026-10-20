(* TEST
 has-z3;
 flags = "-extension refinement_types";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_big_credits.mli vox_big_credits.ml";
 prebuilt_modules += " vox_parallel.mli vox_parallel.ml";
 prebuilt_modules += " vox_span_credits.mli vox_span_credits.ml";
 { bytecode; }
 { native; }
 { multicore; arguments = "parallel"; bytecode; }
 { multicore; arguments = "parallel"; native; }
*)

module S = Vox_span_credits
module C = Vox_big_credits.Make ()

type tree = Leaf of int | Node of tree * tree [@@inductive]

let[@def] max (left : Bigint.t) (right : Bigint.t) =
  if left <= right then right else left

let[@def] rec maximum (tree : tree) =
  match tree with
  | Leaf value -> value
  | Node (left, right) ->
    let l = maximum left in
    let r = maximum right in
    if l <= r then r else l

let[@def] rec size (tree : tree) =
  match tree with
  | Leaf _ -> 1Z
  | Node (left, right) -> Bigint.add 1Z (Bigint.add (size left) (size right))

let[@def] rec height (tree : tree) =
  match tree with
  | Leaf _ -> 1Z
  | Node (left, right) ->
    Bigint.add 1Z (max (height left) (height right))

let rec (dimensions @ total) (tree : tree) :
    {u : unit | 1Z <= height tree && height tree <= size tree} =
  size_def tree;
  height_def tree;
  match tree with
  | Leaf _ -> ()
  | Node (left, right) ->
    dimensions left;
    dimensions right;
    max_def (height left) (height right);
    ()

let rec (reduce @ portable stateless) : (tree : tree) ->
    (limit : {n : Bigint.t | height tree <= n}) @ ghost ->
    {t : C.token | C.credits t = size tree} @ unique immutable total ghost ->
    {n : Bigint.t | n = limit} S.token
      @ local unique nonportable total ghost ->
    {n : int | n = maximum tree} @ portable =
    fun tree limit work span ->
  ghost_ (
    dimensions tree;
    maximum_def tree;
    size_def tree;
    height_def tree);
  let work = C.tick work in
  let span = S.tick limit
    (span :> {n : Bigint.t | n = limit} S.token) in
  match tree with
  | Leaf value -> value
  | Node (left, right) ->
    ghost_ (
      dimensions left;
      dimensions right;
      max_def (height left) (height right));
    let remaining = ghost_ (Bigint.sub limit 1Z) in
    let {C.left = left_work; right = right_work} =
      C.split (ghost_ (size left)) work in
    let l, r = S.fork_join remaining
      (span :> {n : Bigint.t | n = remaining} S.token)
      (fun span : {n : int | n = maximum left} ->
        reduce left remaining left_work span)
      (fun span : {n : int | n = maximum right} ->
        reduce right remaining right_work span) in
    if l <= r then r else l

let evaluate (tree : tree) : {n : int | n = maximum tree} =
  ghost_ (dimensions tree);
  let work = C.Budget.create (ghost_ (size tree)) in
  let limit = ghost_ (height tree) in
  S.run limit (fun span : {n : int | n = maximum tree} ->
    reduce tree limit work span)

let () =
  let left = Node (Leaf (-7), Leaf 42) in
  let right = Node (Leaf 11, Leaf 0) in
  let tree = Node (left, right) in
  ghost_ (
    size_def tree; size_def left; size_def right;
    size_def (Leaf (-7)); size_def (Leaf 42);
    size_def (Leaf 11); size_def (Leaf 0);
    height_def tree; height_def left; height_def right;
    height_def (Leaf (-7)); height_def (Leaf 42);
    height_def (Leaf 11); height_def (Leaf 0);
    max_def 1Z 1Z; max_def 2Z 2Z;
    (() : {u : unit | size tree = 7Z && height tree = 3Z}));
  assert (evaluate (Leaf min_int) = min_int);
  if Array.length Sys.argv > 1 then (
    assert (evaluate tree = 42);
    assert (evaluate (Node (Leaf max_int, Leaf min_int)) = max_int))
