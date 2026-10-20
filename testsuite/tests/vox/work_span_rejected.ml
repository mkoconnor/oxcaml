(* TEST
 has-z3;
 flags = "-extension refinement_types";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_parallel.mli vox_parallel.ml";
 prebuilt_modules += " vox_span_credits.mli vox_span_credits.ml";
 readonly_files = "work_span_rejected.ml";
 { setup-ocamlc.opt-build-env; run-expect; check-program-output; }
*)

#load "vox_parallel.cmo";;
#load "vox_span_credits.cmo";;

module S = Vox_span_credits;;
type packed = { token : Bigint.t S.token @@ ghost };;
type portable_packed = { token : Bigint.t S.token @@ portable ghost };;
[%%expect{|
module S = Vox_span_credits
type packed = { token : Bigint.t S.token @@ ghost; }
type portable_packed = { token : Bigint.t S.token @@ ghost portable; }
|}]

let require_portable
    (_token : Bigint.t S.token @ local portable total ghost) = ();;
let require_portable_record (_packed : packed @ local portable) = ();;
[%%expect{|
val require_portable : Bigint.t S.token @ local total ghost -> unit = <fun>
val require_portable_record : packed @ local portable -> unit = <fun>
|}]

let portable_crossing
    (token : Bigint.t S.token @ unique nonportable total ghost) =
  require_portable token;;
[%%expect{|
Line 3, characters 19-24:
3 |   require_portable token;;
                       ^^^^^
Error: This value is "nonportable" but is expected to be "portable".
|}]

let wrapped_portable_crossing
    (token : Bigint.t S.token @ unique nonportable total ghost) =
  let packed : packed = {token} in
  require_portable_record packed;;
[%%expect{|
Line 4, characters 26-32:
4 |   require_portable_record packed;;
                              ^^^^^^
Error: This value is "nonportable"
         because it is a record whose field "token" is the expression at line 3, characters 25-30
         which is "nonportable".
       However, the highlighted expression is expected to be "portable".
|}]

let portable_field_crossing
    (token : Bigint.t S.token @ unique nonportable total ghost) =
  let (_packed : portable_packed) = {token} in
  ();;
[%%expect{|
Line 3, characters 37-42:
3 |   let (_packed : portable_packed) = {token} in
                                         ^^^^^
Error: This value is "nonportable"
       but is expected to be "portable"
         because it is the field "token" (with some modality) of the record at line 3, characters 36-43.
|}]

let refined_wrapper_crossing
    (token : Bigint.t S.token @ unique nonportable total ghost) =
  let packed : packed = {token} in
  let _ = (packed : {p : packed | true}) in
  ();;
[%%expect{|
Line 4, characters 11-17:
4 |   let _ = (packed : {p : packed | true}) in
               ^^^^^^
Error: This value is "nonportable"
         because it is a record whose field "token" is the expression at line 3, characters 25-30
         which is "nonportable".
       However, the highlighted expression is expected to be "portable".
|}]

let capture_left () =
  let one = ghost_ 1Z in
  let two = ghost_ 2Z in
  S.run two (fun token ->
    let {S.left = reserve; right = outside} = S.split one one
      (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
    let _ = S.fork_join one reserve
      (fun _branch -> let _ = S.tick one outside in ())
      (fun _branch -> ()) in
    ());;
[%%expect{|
Line 8, characters 41-48:
8 |       (fun _branch -> let _ = S.tick one outside in ())
                                             ^^^^^^^
Error: The value "outside" is "nonportable"
         because it is the field "right" of the record at line 5, characters 8-43
         which is "nonportable".
       However, the value "outside" highlighted is expected to be "portable"
         because it is used inside the function at line 8, characters 6-55
         which is expected to be "portable".
|}]

let capture_right () =
  let one = ghost_ 1Z in
  let two = ghost_ 2Z in
  S.run two (fun token ->
    let {S.left = reserve; right = outside} = S.split one one
      (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
    let _ = S.fork_join one reserve
      (fun _branch -> ())
      (fun _branch -> let _ = S.tick one outside in ()) in
    ());;
[%%expect{|
Line 9, characters 41-48:
9 |       (fun _branch -> let _ = S.tick one outside in ()) in
                                             ^^^^^^^
Error: The value "outside" is "nonportable"
         because it is the field "right" of the record at line 5, characters 8-43
         which is "nonportable".
       However, the value "outside" highlighted is expected to be "portable"
         because it is used inside the function at line 9, characters 6-55
         which is expected to be "portable".
|}]

let capture_wrapped () =
  let one = ghost_ 1Z in
  let two = ghost_ 2Z in
  S.run two (fun token ->
    let {S.left = reserve; right = outside} = S.split one one
      (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
    let packed : packed = {token = (outside :> Bigint.t S.token)} in
    let _ = S.fork_join one reserve
      (fun _branch -> let _ = S.credits packed.token in ())
      (fun _branch -> ()) in
    ());;
[%%expect{|
Line 9, characters 40-46:
9 |       (fun _branch -> let _ = S.credits packed.token in ())
                                            ^^^^^^
Error: The value "packed" is "nonportable"
         because it is a record whose field "token" is the expression at line 7, characters 36-43
         which is "nonportable"
         because it is the field "right" of the record at line 5, characters 8-43
         which is "nonportable".
       However, the value "packed" highlighted is expected to be "portable"
         because it is used inside the function at line 9, characters 6-59
         which is expected to be "portable".
|}]

let capture_in_nested_fork () =
  let one = ghost_ 1Z in
  let two = ghost_ 2Z in
  S.run two (fun token ->
    let _ = S.fork_join two token
      (fun branch ->
        let {S.left = reserve; right = outside} = S.split one one
          (branch :> {n : Bigint.t | n = Bigint.add one one} S.token) in
        let _ = S.fork_join one reserve
          (fun _child -> ())
          (fun _child -> let _ = S.tick one outside in ()) in
        ())
      (fun _branch -> ()) in
    ());;
[%%expect{|
Line 11, characters 44-51:
11 |           (fun _child -> let _ = S.tick one outside in ()) in
                                                 ^^^^^^^
Error: The value "outside" is "nonportable"
         because it is the field "right" of the record at line 7, characters 12-47
         which is "nonportable".
       However, the value "outside" highlighted is expected to be "portable"
         because it is used inside the function at line 11, characters 10-58
         which is expected to be "portable".
|}]

let return_token () =
  let one = ghost_ 1Z in
  let _ = S.run one (fun token -> S.tick one token) in
  ();;
[%%expect{|
Line 3, characters 34-50:
3 |   let _ = S.run one (fun token -> S.tick one token) in
                                      ^^^^^^^^^^^^^^^^
Error: This expression has type
         "{k : Bigint.t | k = (Bigint.sub one (Bigint.of_int 1))} S.token" =
           "{k : Bigint.t | k = (Bigint.sub one (Bigint.of_int 1))}
           Vox_span_credits.token"
       but an expression was expected of type "('a : value)"
       The layout of {k : Bigint.t | k = (Bigint.sub one (Bigint.of_int 1))}
                     S.token is void.
       But the layout of {k : Bigint.t
                           | k = (Bigint.sub one (Bigint.of_int 1))}
                         S.token must be a value layout.
|}]

let return_record () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let token = S.tick one token in
    ({token = (token :> Bigint.t S.token)} : packed));;
[%%expect{|
Line 5, characters 15-20:
5 |     ({token = (token :> Bigint.t S.token)} : packed));;
                   ^^^^^
Error: This value is "nonportable"
       but is expected to be "portable"
         because it is the field "token" of the record at line 5, characters 5-42
         which is expected to be "portable".
|}]

let return_closure () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let token = S.tick one token in
    fun () -> let _ = S.credits token in ());;
[%%expect{|
Line 5, characters 32-37:
5 |     fun () -> let _ = S.credits token in ());;
                                    ^^^^^
Error: The value "token" is "nonportable"
       but is expected to be "portable"
         because it is used inside the function at line 5, characters 4-43
         which is expected to be "portable".
|}]

let return_left_record () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.fork_join one token
      (fun branch ->
        let token = S.tick one branch in
        ({token = (token :> Bigint.t S.token)} : packed))
      (fun _branch -> ()) in
    ());;
[%%expect{|
Line 7, characters 19-24:
7 |         ({token = (token :> Bigint.t S.token)} : packed))
                       ^^^^^
Error: This value is "nonportable"
       but is expected to be "portable"
         because it is the field "token" of the record at line 7, characters 9-46
         which is expected to be "portable".
|}]

let return_right_record () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.fork_join one token
      (fun _branch -> ())
      (fun branch ->
        let token = S.tick one branch in
        ({token = (token :> Bigint.t S.token)} : packed)) in
    ());;
[%%expect{|
Line 8, characters 19-24:
8 |         ({token = (token :> Bigint.t S.token)} : packed)) in
                       ^^^^^
Error: This value is "nonportable"
       but is expected to be "portable"
         because it is the field "token" of the record at line 8, characters 9-46
         which is expected to be "portable".
|}]

let duplicate_spending () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.tick one token in
    let _ = S.tick one token in
    ());;
[%%expect{|
Line 5, characters 23-28:
5 |     let _ = S.tick one token in
                           ^^^^^
Error: This value is used here, but it has already been used as unique at:
Line 4, characters 23-28:
4 |     let _ = S.tick one token in
                           ^^^^^

|}]

let duplicate_fork () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.fork_join one token (fun _ -> ()) (fun _ -> ()) in
    let _ = S.fork_join one token (fun _ -> ()) (fun _ -> ()) in
    ());;
[%%expect{|
Line 5, characters 28-33:
5 |     let _ = S.fork_join one token (fun _ -> ()) (fun _ -> ()) in
                                ^^^^^
Error: This value is used here, but it has already been used as unique at:
Line 4, characters 28-33:
4 |     let _ = S.fork_join one token (fun _ -> ()) (fun _ -> ()) in
                                ^^^^^

|}]

let empty_spending () =
  let zero = ghost_ 0Z in
  S.run zero (fun token -> let _ = S.tick zero token in ());;
[%%expect{|
Line 3, characters 42-46:
3 |   S.run zero (fun token -> let _ = S.tick zero token in ());;
                                              ^^^^
Error: Refinement could not be proved (counterexample)
File "vox_span_credits.mli", line 15, characters 32-38:
  The refinement is stated here.
|}]

let unfunded_spending () =
  let zero = ghost_ 0Z in
  let one = ghost_ 1Z in
  S.run zero (fun token ->
    let _ = S.tick one
      (token :> {n : Bigint.t | n = one} S.token) in
    ());;
[%%expect{|
Line 6, characters 6-49:
6 |       (token :> {n : Bigint.t | n = one} S.token) in
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: element = 0Z)
Line 6, characters 32-39:
6 |       (token :> {n : Bigint.t | n = one} S.token) in
                                    ^^^^^^^
  The refinement is stated here.
|}]

let unfunded_split () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.split one one
      (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
    ());;
[%%expect{|
Line 5, characters 6-64:
5 |       (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: element = 1Z)
Line 5, characters 32-54:
5 |       (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
                                    ^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

let duplicate_merge () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.merge one one token token in
    ());;
[%%expect{|
Line 4, characters 34-39:
4 |     let _ = S.merge one one token token in
                                      ^^^^^
Error: This value is used here, but it is also being used as unique at:
Line 4, characters 28-33:
4 |     let _ = S.merge one one token token in
                                ^^^^^

|}]

let unfunded_merge () =
  let one = ghost_ 1Z in
  let two = ghost_ 2Z in
  S.run two (fun token ->
    let {S.left; right} = S.split one one
      (token :> {n : Bigint.t | n = Bigint.add one one} S.token) in
    let left = S.tick one left in
    let _ = S.merge one one
      (left :> {n : Bigint.t | n = one} S.token) right in
    ());;
[%%expect{|
Line 9, characters 6-48:
9 |       (left :> {n : Bigint.t | n = one} S.token) right in
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Refinement could not be proved (counterexample: element = 0Z)
Line 9, characters 31-38:
9 |       (left :> {n : Bigint.t | n = one} S.token) right in
                                   ^^^^^^^
  The refinement is stated here.
|}]

let nested_run () =
  let zero = ghost_ 0Z in
  let one = ghost_ 1Z in
  S.run zero (fun _token ->
    S.run one (fun inner -> let _ = S.tick one inner in ()));;
[%%expect{|
Line 5, characters 4-9:
5 |     S.run one (fun inner -> let _ = S.tick one inner in ()));;
        ^^^^^
Error: The value "S.run" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at lines 4-5, characters 13-60
         which is expected to be "stateless".
|}]

let mutable_read (cell : int ref) =
  let zero = ghost_ 0Z in
  S.run zero (fun _token -> !cell);;
[%%expect{|
Line 3, characters 28-29:
3 |   S.run zero (fun _token -> !cell);;
                                ^
Error: The value "(!)" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at line 3, characters 13-34
         which is expected to be "stateless".
|}]

let mutable_write (cell : int ref) =
  let zero = ghost_ 0Z in
  S.run zero (fun _token -> cell := 1);;
[%%expect{|
Line 3, characters 33-35:
3 |   S.run zero (fun _token -> cell := 1);;
                                     ^^
Error: The value "(:=)" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at line 3, characters 13-38
         which is expected to be "stateless".
|}]

let atomic_read (cell : int Atomic.t) =
  let zero = ghost_ 0Z in
  S.run zero (fun _token -> Atomic.get cell);;
[%%expect{|
Line 3, characters 28-38:
3 |   S.run zero (fun _token -> Atomic.get cell);;
                                ^^^^^^^^^^
Error: The value "Atomic.get" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at line 3, characters 13-44
         which is expected to be "stateless".
|}]

let atomic_synchronization (ready : bool Atomic.t) =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let _ = S.fork_join one token
      (fun branch ->
        let _ = S.tick one branch in
        Atomic.set ready true)
      (fun branch ->
        while not (Atomic.get ready) do () done;
        let _ = S.tick one branch in
        ()) in
    ());;
[%%expect{|
Line 7, characters 8-18:
7 |         Atomic.set ready true)
            ^^^^^^^^^^
Error: The value "Atomic.set" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at lines 3-12, characters 12-7
         which is expected to be "stateless".
|}]

let raw_fork_capture
    (token : {n : Bigint.t | n = 1Z} S.token
      @ unique nonportable total ghost) =
  let one = ghost_ 1Z in
  Vox_parallel.fork_join
    (fun () ->
      let _ = S.tick one (token :> {n : Bigint.t | n = one} S.token) in
      ())
    (fun () -> ());;
[%%expect{|
Line 7, characters 26-31:
7 |       let _ = S.tick one (token :> {n : Bigint.t | n = one} S.token) in
                              ^^^^^
Error: The value "token" is "nonportable"
       but is expected to be "portable"
         because it is used inside the function at lines 6-8, characters 4-9
         which is expected to be "portable".
|}]

let raw_fork_inside_run () =
  let zero = ghost_ 0Z in
  S.run zero (fun _token ->
    let _ = Vox_parallel.fork_join (fun () -> ()) (fun () -> ()) in
    ());;
[%%expect{|
Line 4, characters 12-34:
4 |     let _ = Vox_parallel.fork_join (fun () -> ()) (fun () -> ()) in
                ^^^^^^^^^^^^^^^^^^^^^^
Error: The value "Vox_parallel.fork_join" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at lines 3-5, characters 13-7
         which is expected to be "stateless".
|}]

let fork_in_ghost
    (token : {n : Bigint.t | n = 1Z} S.token
      @ local unique nonportable total ghost) =
  let one = ghost_ 1Z in
  ghost_ (S.fork_join one
    (token :> {n : Bigint.t | n = one} S.token)
    (fun _ -> ()) (fun _ -> ()));;
[%%expect{|
Line 5, characters 10-21:
5 |   ghost_ (S.fork_join one
              ^^^^^^^^^^^
Error: The value "S.fork_join" is "partial"
       but is expected to be "total"
         because it is used in an expression (at lines 5-7, characters 2-32).
|}]

let (fork_in_total @ total stateful)
    (token : {n : Bigint.t | n = 1Z} S.token
      @ local unique nonportable total ghost) =
  let one = ghost_ 1Z in
  let _ = S.fork_join one
    (token :> {n : Bigint.t | n = one} S.token)
    (fun _ -> ()) (fun _ -> ()) in
  ();;
[%%expect{|
Line 5, characters 10-21:
5 |   let _ = S.fork_join one
              ^^^^^^^^^^^
Error: The value "S.fork_join" is "partial"
       but is expected to be "total"
         because it is used inside the function at lines 2-8, characters 4-4
         which is expected to be "total".
|}]

let mint () = S.Budget.create 1Z;;
[%%expect{|
Line 1, characters 14-22:
1 | let mint () = S.Budget.create 1Z;;
                  ^^^^^^^^
Error: Unbound module "S.Budget"
|}]

let forge () : Bigint.t S.token = ();;
[%%expect{|
Line 1, characters 34-36:
1 | let forge () : Bigint.t S.token = ();;
                                      ^^
Error: The constructor "()" has type "unit"
       but an expression was expected of type
         "Bigint.t S.token" = "Bigint.t Vox_span_credits.token"
|}]

type full =
  { value : int; full : {n : Bigint.t | n = 1Z} S.token @@ ghost };;
exception Carry of full;;
[%%expect{|
type full = {
  value : int;
  full : {n : Bigint.t | n = (Bigint.of_int 1)} S.token @@ ghost;
}
exception Carry of full
|}]

let exception_pack () =
  let one = ghost_ 1Z in
  S.run one (fun token ->
    let full = (token :> {n : Bigint.t | n = 1Z} S.token) in
    raise (Carry {value = 0; full}));;
[%%expect{|
Line 5, characters 4-9:
5 |     raise (Carry {value = 0; full}));;
        ^^^^^
Error: The value "raise" is "stateful"
       but is expected to be "stateless"
         because it is used inside the function at lines 3-5, characters 12-36
         which is expected to be "stateless".
|}]

let exception_unpack (exn : exn @ aliased) =
  let one = ghost_ 1Z in
  match exn with
  | Carry {full; _} ->
    let _ = S.tick one (full :> {n : Bigint.t | n = one} S.token) in
    ()
  | _ -> ();;
[%%expect{|
Line 5, characters 24-28:
5 |     let _ = S.tick one (full :> {n : Bigint.t | n = one} S.token) in
                            ^^^^
Error: This value is "aliased"
         because it is the field "full" of the record at line 4, characters 10-19
         which is "aliased"
         because it is contained (via constructor "Carry") in the value at line 4, characters 4-19
         which is "aliased".
       However, the highlighted expression is expected to be "unique".
|}]
