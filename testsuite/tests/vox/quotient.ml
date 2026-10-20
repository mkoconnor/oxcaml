(* TEST
 has-z3;
 flags = "-extension refinement_types -principal";
 source_directories = "${test_source_directory}/../../../verification/library";
 prebuilt_modules = "vox_quotient.mli vox_quotient.ml";
 { bytecode; }
 { native; }
*)

module Fraction = struct
  type t = {
    numerator : Bigint.t;
    denominator : {n : Bigint.t | n > 0Z}
  }

  let[@def] equal (x : t) (y : t) =
    Bigint.mul x.numerator y.denominator =
      Bigint.mul y.numerator x.denominator

  let (reflexive @ total) (x : t) : {u : unit | equal x x} =
    equal_def x x; ()

  let (symmetric @ total) (x : t) (y : t) :
      {u : unit | equal x y = equal y x} =
    equal_def x y; equal_def y x; ()

  let (transitive @ total) (x : t) (y : t) (z : t) :
      {u : unit | not (equal x y && equal y z) || equal x z} =
    let _ = y.denominator in
    equal_def x y; equal_def y z; equal_def x z; ()
end

module Q = Vox_quotient.Make (Fraction)
module Alias = Q
module Ascribed : module type of Q = Q

module Sign = struct
  type result = bool
  let[@def] (f @ total) (x : Fraction.t) : bool @ ghost =
    ghost_ (x.numerator >= 0Z)
  let (respects @ total) (x : Fraction.t) (y : Fraction.t) :
      {u : unit | not (Fraction.equal x y) || f x === f y}
      @ ghost = ghost_ (
    let _ = x.denominator in
    let _ = y.denominator in
    Fraction.equal_def x y; f_def x; f_def y; ())
end

module Nonnegative = Q.Lift (Sign)

module Sum = struct
  type result = Q.t
  let[@def] add (x : Fraction.t) (y : Fraction.t) : Fraction.t =
    { numerator = Bigint.add
        (Bigint.mul x.numerator y.denominator)
        (Bigint.mul y.numerator x.denominator);
      denominator = Bigint.mul x.denominator y.denominator }
  let[@def] (f @ total) (x : Fraction.t) (y : Fraction.t) : result
      @ ghost = ghost_ (Q.class_of (add x y))
  let (respects @ total) (x : Fraction.t) (x' : Fraction.t)
      (y : Fraction.t) (y' : Fraction.t) :
      {u : unit | not (Fraction.equal x x' && Fraction.equal y y') ||
        f x y === f x' y'} @ ghost = ghost_ (
    f_def x y; f_def x' y';
    add_def x y; add_def x' y';
    Fraction.equal_def x x'; Fraction.equal_def y y';
    Fraction.equal_def (add x y) (add x' y');
    Q.class_equal (add x y) (add x' y'); ())
end

module Add = Q.Lift2 (Sum)

module Reclassify = struct
  type result = Q.t
  let[@def] (f @ total) (x : Fraction.t) : result @ ghost =
    ghost_ (Q.class_of x)
  let (respects @ total) (x : Fraction.t) (y : Fraction.t) :
      {u : unit | not (Fraction.equal x y) || f x === f y}
      @ ghost = ghost_ (
    f_def x; f_def y; Q.class_equal x y; ())
end

module Identity = Q.Lift (Reclassify)
module Identity_property = struct
  let[@def] (predicate @ total) (q : Q.t) : bool @ ghost =
    ghost_ (Identity.apply q === q)
  let (case @ total) (x : Fraction.t) :
      {u : unit | predicate (Q.class_of x)} @ ghost = ghost_ (
    predicate_def (Q.class_of x);
    Identity.beta x; Reclassify.f_def x; ())
end

let (identity @ total) (q : Q.t) :
    {u : unit | Identity.apply q === q} @ ghost = ghost_ (
  Q.induct q Identity_property.predicate Identity_property.case;
  Identity_property.predicate_def q; ())

let (examples @ total) () : unit @ ghost = ghost_ (
  let half : Fraction.t = {numerator = 1Z; denominator = 2Z} in
  let twice : Fraction.t = {numerator = 2Z; denominator = 4Z} in
  let third : Fraction.t = {numerator = 1Z; denominator = 3Z} in
  let sum : Fraction.t = {numerator = 5Z; denominator = 6Z} in
  Fraction.equal_def half twice;
  Fraction.equal_def half third;
  Q.class_equal half twice; Q.class_equal half third;
  let (_ : {u : unit | Alias.class_of half === Ascribed.class_of twice
      && not (Q.class_of half === Q.class_of third)}) = () in
  Nonnegative.beta twice; Sign.f_def twice;
  let (_ : {u : unit | Nonnegative.apply (Q.class_of half)}) = () in
  Add.beta half third; Sum.f_def half third; Sum.add_def half third;
  Q.class_equal (Sum.add half third) sum;
  Fraction.equal_def (Sum.add half third) sum;
  let (_ : {u : unit | Add.apply (Q.class_of half) (Q.class_of third)
      === Q.class_of sum}) = () in
  identity (Q.class_of half))

module Empty = struct
  type t = {x : int | false}
  let[@def] equal (_ : t) (_ : t) = true
  let (reflexive @ total) (x : t) : {u : unit | equal x x} = ()
  let (symmetric @ total) (x : t) (y : t) :
      {u : unit | equal x y = equal y x} = ()
  let (transitive @ total) (x : t) (y : t) (z : t) :
      {u : unit | not (equal x y && equal y z) || equal x z} = ()
end

module Empty_quotient = Vox_quotient.Make (Empty)
module Empty_property = struct
  let[@def] (predicate @ total) (_q : Empty_quotient.t) : bool @ ghost =
    ghost_ (false)
  let (case @ total) (x : Empty.t) :
      {u : unit | predicate (Empty_quotient.class_of x)} @ ghost = ghost_ ()
end

let (empty @ total) (q : Empty_quotient.t) :
    {u : unit | false} @ ghost = ghost_ (
  Empty_quotient.induct q Empty_property.predicate Empty_property.case;
  Empty_property.predicate_def q; ())

let () = ghost_ (examples ()); ()
