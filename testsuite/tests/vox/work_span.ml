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

let rec (steps @ portable total) :
    (count : {n : int | 0 <= n}) ->
    (limit : {n : Bigint.t | Bigint.of_int count <= n}) @ ghost ->
    (work : {t : C.token | Bigint.of_int count <= C.credits t})
      @ unique immutable total ghost ->
    {n : Bigint.t | n = limit} S.token
      @ local unique nonportable total ghost ->
    {t : C.token | C.credits t =
      Bigint.sub (C.credits work) (Bigint.of_int count)}
      @ unique immutable total ghost = fun count limit work span ->
  if count = 0 then work
  else
    let span = S.tick limit
      (span :> {n : Bigint.t | n = limit} S.token) in
    let work = C.tick work in
    let remaining = ghost_ (Bigint.sub limit 1Z) in
    steps (count - 1) remaining work
      (span :> {n : Bigint.t | n = remaining} S.token)
[@@decreases count]

let () =
  let budget = ghost_ 8Z in
  let three = ghost_ 3Z in
  let five = ghost_ 5Z in
  let work = C.Budget.create 10Z in
  S.run budget (fun span ->
    let {S.left; right} = S.split three five
      (span :> {n : Bigint.t | n = Bigint.add three five} S.token) in
    let work = steps 3 three work left in
    let work = steps 5 five work right in
    ghost_ ((() : {u : unit | C.credits work = 2Z}));
    ())

let () =
  let five = ghost_ 5Z in
  let two = ghost_ 2Z in
  let three = ghost_ 3Z in
  S.run five (fun span ->
    let {S.left; right} = S.split two three
      (span :> {n : Bigint.t | n = Bigint.add two three} S.token) in
    let span = S.merge two three left right in
    let balance = S.credits (borrow_ span) in
    ghost_ ((() : {u : unit | balance = 5Z}));
    ())

let () =
  if Array.length Sys.argv > 1 then (
    let seven = ghost_ 7Z in
    let five = ghost_ 5Z in
    let two = ghost_ 2Z in
    let work = C.Budget.create 10Z in
    S.run seven (fun span ->
      let {S.left = fork; right = reserve} = S.split five two
        (span :> {n : Bigint.t | n = Bigint.add five two} S.token) in
      let {C.left = branch_work; right = continuation_work} =
        C.split (ghost_ 8Z) work in
      let {C.left = left_work; right = right_work} =
        C.split (ghost_ 3Z) branch_work in
      let (), () = S.fork_join five fork
        (fun span ->
          let work = steps 3 five left_work span in
          ghost_ ((() : {u : unit | C.credits work = 0Z}));
          ())
        (fun span ->
          let work = steps 5 five right_work span in
          ghost_ ((() : {u : unit | C.credits work = 0Z}));
          ()) in
      let work = steps 2 two continuation_work reserve in
      ghost_ ((() : {u : unit | C.credits work = 0Z}));
      ()))

type ('n : logical_data) delayed =
  { value : int; potential : 'n S.token @@ ghost }

let () =
  let one = ghost_ 1Z in
  let value = S.run one (fun span ->
    let local_ delayed = { value = 42; potential = span } in
    let span = S.tick one delayed.potential in
    let balance = S.credits (borrow_ span) in
    ghost_ ((() : {u : unit | balance = 0Z}));
    delayed.value) in
  assert (value = 42)
