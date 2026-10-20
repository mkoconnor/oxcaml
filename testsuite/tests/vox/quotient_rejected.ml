(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_quotient.mli vox_quotient.ml";
 prebuilt_modules += " vox_big_credits.mli vox_big_credits.ml";
 readonly_files = "quotient_rejected.ml";
 { setup-ocamlc.opt-build-env; run-expect; check-program-output; }
*)

#load "vox_quotient.cmo";;
#load "vox_big_credits.cmo";;

module Key = struct
  type t = { value : int; ignored : int }
  let[@def] equal (x : t) (y : t) = x.value = y.value
  let (reflexive @ total) (x : t) : {u : unit | equal x x} =
    equal_def x x; ()
  let (symmetric @ total) (x : t) (y : t) :
      {u : unit | equal x y = equal y x} =
    equal_def x y; equal_def y x; ()
  let (transitive @ total) (x : t) (y : t) (z : t) :
      {u : unit | not (equal x y && equal y z) || equal x z} =
    equal_def x y; equal_def y z; equal_def x z; ()
end;;
module Q = Vox_quotient.Make (Key);;
[%%expect{|
module Key :
  sig
    type t = { value : int; ignored : int; }
    val equal : t -> t -> bool
    val equal_def :
      (x : t) -> (y : t) -> {u : unit | (equal x y) === (x.value = y.value)}
    val reflexive : (x : t) -> {u : unit | equal x x}
    val symmetric :
      (x : t) -> (y : t) -> {u : unit | (equal x y) = (equal y x)}
    val transitive :
      (x : t) ->
      (y : t) ->
      (z : t) ->
      {u : unit | (not ((equal x y) && (equal y z))) || (equal x z)}
  end
module Q :
  sig
    type t = Vox_quotient.Make(Key).t
    val class_of : Key.t -> t @ ghost @@ total
    val class_equal :
      (x : Key.t) ->
      (y : Key.t) ->
      {u : unit | ((class_of x) === (class_of y)) = (Key.equal x y)} @ ghost
      @@ total
    module Lift :
      functor
        (F : sig
               type result : logical_data
               val f : Key.t -> result @ ghost @@ total
               val respects :
                 (x : Key.t) ->
                 (y : Key.t) ->
                 {u : unit | (not (Key.equal x y)) || ((f x) === (f y))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> F.result @ ghost @@ total
          val beta :
            (x : Key.t) ->
            {u : unit | (apply (class_of x)) === (F.f x)} @ ghost @@ total
        end
    module Lift2 :
      functor
        (F : sig
               type result : logical_data
               val f : Key.t -> Key.t -> result @ ghost @@ total
               val respects :
                 (x : Key.t) ->
                 (x' : Key.t) ->
                 (y : Key.t) ->
                 (y' : Key.t) ->
                 {u : unit
                   | (not ((Key.equal x x') && (Key.equal y y'))) ||
                       ((f x y) === (f x' y'))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> t -> F.result @ ghost @@ total
          val beta :
            (x : Key.t) ->
            (y : Key.t) ->
            {u : unit | (apply (class_of x) (class_of y)) === (F.f x y)} @ ghost
            @@ total
        end
    val induct :
      (q : t) ->
      (predicate : (t -> bool @ ghost)) ->
      ((x : Key.t) -> {u : unit | predicate (class_of x)} @ ghost) @ total ->
      {u : unit | predicate q} @ ghost @@ total
  end
|}]

let (collapse @ total) () :
    {u : unit | Q.class_of {value = 0; ignored = 0} ===
      Q.class_of {value = 1; ignored = 0}} @ ghost = ghost_ (
  let x : Key.t = {value = 0; ignored = 0} in
  let y : Key.t = {value = 1; ignored = 0} in
  Key.equal_def x y; Q.class_equal x y; ());;
[%%expect{|
Line 6, characters 40-42:
6 |   Key.equal_def x y; Q.class_equal x y; ());;
                                            ^^
Error: Refinement could not be proved (counterexample)
Lines 2-3, characters 16-41:
2 | ................Q.class_of {value = 0; ignored = 0} ===
3 |       Q.class_of {value = 1; ignored = 0}....................
  The refinement is stated here.
|}]

module Projection = struct
  type result = int
  let[@def] (f @ total) (x : Key.t) : result @ ghost =
    ghost_ (x.ignored)
  let (respects @ total) (x : Key.t) (y : Key.t) :
      {u : unit | not (Key.equal x y) || f x === f y} @ ghost = ghost_ (
    Key.equal_def x y; f_def x; f_def y; ())
end;;
[%%expect{|
Line 7, characters 41-43:
7 |     Key.equal_def x y; f_def x; f_def y; ())
                                             ^^
Error: Refinement could not be proved (counterexample)
Line 6, characters 18-52:
6 |       {u : unit | not (Key.equal x y) || f x === f y} @ ghost = ghost_ (
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  The refinement is stated here.
|}]

module False_equivalence = struct
  type t = int
  let[@def] equal (_x : int) (_y : int) = false
  let (reflexive @ total) (x : int) : {u : unit | equal x x} =
    equal_def x x; ()
end;;
[%%expect{|
Line 5, characters 19-21:
5 |     equal_def x x; ()
                       ^^
Error: Refinement could not be proved (counterexample: x = 0)
Line 4, characters 50-59:
4 |   let (reflexive @ total) (x : int) : {u : unit | equal x x} =
                                                      ^^^^^^^^^
  The refinement is stated here.
|}]

module Missing_laws = Vox_quotient.Make (struct
  type t = int
  let (equal @ total) (x : int) (y : int) = x = y
end);;
[%%expect{|
Lines 1-4, characters 22-4:
1 | ......................Vox_quotient.Make (struct
2 |   type t = int
3 |   let (equal @ total) (x : int) (y : int) = x = y
4 | end)..
Error: Modules do not match:
       sig type t = int val equal : int -> int -> bool end
     is not included in
       sig
         type t : logical_data
         val equal : t -> t -> bool @@ total
         val reflexive : (x : t) -> {u : unit | equal x x} @@ total
         val symmetric :
           (x : t) -> (y : t) -> {u : unit | (equal x y) = (equal y x)} @@
           total
         val transitive :
           (x : t) ->
           (y : t) ->
           (z : t) ->
           {u : unit | (not ((equal x y) && (equal y z))) || (equal x z)} @@
           total
       end
     The value "reflexive" is required but not provided
     File "map.mli", line 485, characters 2-60: Expected declaration
     The value "symmetric" is required but not provided
     File "map.mli", lines 486-487, characters 2-47: Expected declaration
     The value "transitive" is required but not provided
     File "map.mli", lines 488-489, characters 2-67: Expected declaration
|}]

let escape (x : Key.t) : Q.t @ real = Q.class_of x;;
[%%expect{|
Line 1, characters 38-50:
1 | let escape (x : Key.t) : Q.t @ real = Q.class_of x;;
                                          ^^^^^^^^^^^^
Error: This value is "ghost" but is expected to be "real".
|}]

let representative (q : Q.t) = Q.representative q;;
[%%expect{|
Line 1, characters 31-47:
1 | let representative (q : Q.t) = Q.representative q;;
                                   ^^^^^^^^^^^^^^^^
Error: Unbound value "Q.representative"
|}]

module M = Map.MakeLogical (Key);;
let (forge @ total) (x : Key.t) : Q.t @ ghost =
  ghost_ (M.add x () (M.empty ()));;
[%%expect{|
module M :
  sig
    type ('a : immutable_data) t = 'a Map.MakeLogical(Key).t
    external empty : ('a : immutable_data). unit -> 'a t @ ghost @@ total
      = "caml_logical_map_empty"
    external find_opt :
      ('a : immutable_data). Key.t -> 'a t -> 'a option @ ghost @@ total
      = "caml_logical_map_find_opt"
    external mem : ('a : immutable_data). Key.t -> 'a t -> bool @ ghost @@
      total = "caml_logical_map_mem"
    external add : ('a : immutable_data). Key.t -> 'a -> 'a t -> 'a t @ ghost
      @@ total = "caml_logical_map_add"
    external remove : ('a : immutable_data). Key.t -> 'a t -> 'a t @ ghost @@
      total = "caml_logical_map_remove"
    external cardinal :
      ('a : immutable_data).
        'a t -> {n : Bigint.t | (Bigint.of_int 0) <= n} @ ghost
      @@ total = "caml_logical_map_cardinal"
    module Proof :
      sig
        external difference :
          ('a : immutable_data).
            (left : 'a t) ->
            (right : 'a t) ->
            {result : Key.t option
              | match result with
                | None -> left === right
                | Some key ->
                    not ((find_opt key left) === (find_opt key right))} @ ghost
          @@ total = "caml_logical_map_difference"
      end
  end
Line 3, characters 9-34:
3 |   ghost_ (M.add x () (M.empty ()));;
             ^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This expression has type "unit M.t" = "unit Map.MakeLogical(Key).t"
       but an expression was expected of type "Q.t" = "Vox_quotient.Make(Key).t"
|}]

module Ascribed : module type of Q = Q;;
let (ascribed_forge @ total) (x : Key.t) : Ascribed.t @ ghost =
  ghost_ (M.add x () (M.empty ()));;
[%%expect{|
module Ascribed :
  sig
    type t = Vox_quotient.Make(Key).t
    val class_of : Key.t -> t @ ghost @@ total
    val class_equal :
      (x : Key.t) ->
      (y : Key.t) ->
      {u : unit | ((class_of x) === (class_of y)) = (Key.equal x y)} @ ghost
      @@ total
    module Lift :
      functor
        (F : sig
               type result : logical_data
               val f : Key.t -> result @ ghost @@ total
               val respects :
                 (x : Key.t) ->
                 (y : Key.t) ->
                 {u : unit | (not (Key.equal x y)) || ((f x) === (f y))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> F.result @ ghost @@ total
          val beta :
            (x : Key.t) ->
            {u : unit | (apply (class_of x)) === (F.f x)} @ ghost @@ total
        end
    module Lift2 :
      functor
        (F : sig
               type result : logical_data
               val f : Key.t -> Key.t -> result @ ghost @@ total
               val respects :
                 (x : Key.t) ->
                 (x' : Key.t) ->
                 (y : Key.t) ->
                 (y' : Key.t) ->
                 {u : unit
                   | (not ((Key.equal x x') && (Key.equal y y'))) ||
                       ((f x y) === (f x' y'))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> t -> F.result @ ghost @@ total
          val beta :
            (x : Key.t) ->
            (y : Key.t) ->
            {u : unit | (apply (class_of x) (class_of y)) === (F.f x y)} @ ghost
            @@ total
        end
    val induct :
      (q : t) ->
      (predicate : (t -> bool @ ghost)) ->
      ((x : Key.t) -> {u : unit | predicate (class_of x)} @ ghost) @ total ->
      {u : unit | predicate q} @ ghost @@ total
  end
Line 3, characters 9-34:
3 |   ghost_ (M.add x () (M.empty ()));;
             ^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This expression has type "unit M.t" = "unit Map.MakeLogical(Key).t"
       but an expression was expected of type
         "Ascribed.t" = "Vox_quotient.Make(Key).t"
|}]

module C = Vox_big_credits.Make ();;
let capture (token : {t : C.token | C.credits t > 0Z}
    @ unique total ghost) =
  let module F = struct
    type result = unit
    let (f @ total) (_x : Key.t) : result @ ghost = ghost_ (
      let _ = C.tick token in ())
    let (respects @ total) (x : Key.t) (y : Key.t) :
        {u : unit | not (Key.equal x y) || f x === f y}
        @ ghost = ghost_ ()
  end in
  let module L = Q.Lift (F) in
  ();;
[%%expect{|
module C :
  sig
    type token : void mod logical
    type partition = { left : token @@ ghost; right : token @@ ghost; }
    val credits : token @ local total immutable ghost -> Bigint.t @ ghost @@
      total
    val nonnegative :
      (token : token) @ local immutable ghost ->
      {u : unit | (Bigint.of_int 0) <= (credits token)} @ ghost @@ total
    val empty :
      unit -> {t : token | (credits t) = (Bigint.of_int 0)} @ unique total
      ghost @@ total
    val tick :
      (token : {t : token | (credits t) > (Bigint.of_int 0)}) @ unique
      immutable ghost ->
      {t : token
        | (credits t) = (Bigint.sub (credits token) (Bigint.of_int 1))} @ unique
      total ghost @@ total
    val split :
      (amount : Bigint.t) @ ghost ->
      (token : {t : token
                 | ((Bigint.of_int 0) <= amount) && (amount <= (credits t))}) @ unique
      immutable ghost ->
      {p : partition
        | ((credits p.left) = amount) &&
            ((credits p.right) = (Bigint.sub (credits token) amount))} @ unique
      @@ total
    val merge :
      (left : token) @ unique immutable ghost ->
      (right : {t : token
                 | ((Bigint.of_int 0) <= (credits left)) &&
                     ((Bigint.of_int 0) <= (credits t))}) @ unique
      immutable ghost ->
      {t : token | (credits t) = (Bigint.add (credits left) (credits right))} @ unique
      total ghost @@ total
    module Budget :
      sig
        val create :
          (amount : {n : Bigint.t | n >= (Bigint.of_int 0)}) @ ghost ->
          {t : token | (credits t) = amount} @ unique total ghost @@ total
      end
  end
Line 7, characters 21-26:
7 |       let _ = C.tick token in ())
                         ^^^^^
Error: This value is "aliased"
         because it is used in an expression (at lines 6-7, characters 52-33).
       However, the highlighted expression is expected to be "unique".
|}]

module Empty = struct
  type t = {x : int | false}
  let[@def] equal (_x : t) (_y : t) = true
  let (reflexive @ total) (x : t) : {u : unit | equal x x} = ()
  let (symmetric @ total) (x : t) (y : t) :
      {u : unit | equal x y = equal y x} = ()
  let (transitive @ total) (x : t) (y : t) (z : t) :
      {u : unit | not (equal x y && equal y z) || equal x z} = ()
end;;
module Empty_quotient = Vox_quotient.Make (Empty);;
[%%expect{|
module Empty :
  sig
    type t = {x : int | false}
    val equal : t -> t -> bool
    val equal_def :
      (_x : t) -> (_y : t) -> {u : unit | (equal _x _y) === true}
    val reflexive : (x : t) -> {u : unit | equal x x}
    val symmetric :
      (x : t) -> (y : t) -> {u : unit | (equal x y) = (equal y x)}
    val transitive :
      (x : t) ->
      (y : t) ->
      (z : t) ->
      {u : unit | (not ((equal x y) && (equal y z))) || (equal x z)}
  end
module Empty_quotient :
  sig
    type t = Vox_quotient.Make(Empty).t
    val class_of : Empty.t -> t @ ghost @@ total
    val class_equal :
      (x : Empty.t) ->
      (y : Empty.t) ->
      {u : unit | ((class_of x) === (class_of y)) = (Empty.equal x y)} @ ghost
      @@ total
    module Lift :
      functor
        (F : sig
               type result : logical_data
               val f : Empty.t -> result @ ghost @@ total
               val respects :
                 (x : Empty.t) ->
                 (y : Empty.t) ->
                 {u : unit | (not (Empty.equal x y)) || ((f x) === (f y))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> F.result @ ghost @@ total
          val beta :
            (x : Empty.t) ->
            {u : unit | (apply (class_of x)) === (F.f x)} @ ghost @@ total
        end
    module Lift2 :
      functor
        (F : sig
               type result : logical_data
               val f : Empty.t -> Empty.t -> result @ ghost @@ total
               val respects :
                 (x : Empty.t) ->
                 (x' : Empty.t) ->
                 (y : Empty.t) ->
                 (y' : Empty.t) ->
                 {u : unit
                   | (not ((Empty.equal x x') && (Empty.equal y y'))) ||
                       ((f x y) === (f x' y'))} @ ghost
                 @@ total
             end)
        ->
        sig
          val apply : t -> t -> F.result @ ghost @@ total
          val beta :
            (x : Empty.t) ->
            (y : Empty.t) ->
            {u : unit | (apply (class_of x) (class_of y)) === (F.f x y)} @ ghost
            @@ total
        end
    val induct :
      (q : t) ->
      (predicate : (t -> bool @ ghost)) ->
      ((x : Empty.t) -> {u : unit | predicate (class_of x)} @ ghost) @ total ->
      {u : unit | predicate q} @ ghost @@ total
  end
|}]

let (inhabit_empty @ total) () : Empty_quotient.t @ ghost =
  ghost_ (Empty_quotient.class_of 0);;
[%%expect{|
Line 2, characters 34-35:
2 |   ghost_ (Empty_quotient.class_of 0);;
                                      ^
Error: Refinement could not be proved (counterexample)
Line 2, characters 22-27:
2 |   type t = {x : int | false}
                          ^^^^^
  The refinement is stated here.
|}]

let (erase_representative @ total) (x : Key.t) : Key.t @ ghost =
  ghost_ ((Q.class_of x :> Key.t));;
[%%expect{|
Line 2, characters 9-34:
2 |   ghost_ ((Q.class_of x :> Key.t));;
             ^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Type "Q.t" = "Vox_quotient.Make(Key).t" is not a subtype of "Key.t"
|}]

module Stateful_equivalence = struct
  type t = int
  let state = ref 0
  let (equal @ total) (x : t) (y : t) =
    x = y && !state = 0
end;;
[%%expect{|
Line 5, characters 13-14:
5 |     x = y && !state = 0
                 ^
Error: The value "(!)" is "partial"
       but is expected to be "total"
         because it is used inside the function at lines 4-5, characters 22-23
         which is expected to be "total".
|}]

module Partial_witness = Q.Lift (struct
  type result = unit
  let (f @ total) (_x : Key.t) : result @ ghost = ghost_ ()
  let respects (_x : Key.t) (_y : Key.t) : unit @ ghost =
    ghost_ (raise Exit)
end);;
[%%expect{|
Line 5, characters 12-17:
5 |     ghost_ (raise Exit)
                ^^^^^
Error: The value "raise" is "partial"
       but is expected to be "total"
         because it is used in an expression (at line 5, characters 4-23).
|}]
