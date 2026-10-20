@@ portable

(** Erased quotient values with logical equality [===]. The equivalence
    witnesses and all lifted operations are checked by the verifier. *)
module Make (E : sig @@ portable include Map.EquatableType end) : sig
  type t : logical_data

  val class_of : E.t -> t @ ghost @@ total

  (** Logical equality of classes is exactly the supplied equivalence. *)
  val class_equal : (x : E.t) -> (y : E.t) ->
    {u : unit | (class_of x === class_of y) = E.equal x y} @ ghost @@ total

  (** Lift a function whose result is independent of the representative. *)
  module Lift (F : sig @@ portable
    type result : logical_data
    val f : E.t -> result @ ghost @@ total
    val respects : (x : E.t) -> (y : E.t) ->
      {u : unit | not (E.equal x y) || f x === f y} @ ghost @@ total
  end) : sig
    val apply : t -> F.result @ ghost @@ total
    val beta : (x : E.t) ->
      {u : unit | apply (class_of x) === F.f x} @ ghost @@ total
  end

  (** Lift a binary function that respects equivalence in both arguments. *)
  module Lift2 (F : sig @@ portable
    type result : logical_data
    val f : E.t -> E.t -> result @ ghost @@ total
    val respects : (x : E.t) -> (x' : E.t) ->
      (y : E.t) -> (y' : E.t) ->
      {u : unit | not (E.equal x x' && E.equal y y') ||
        f x y === f x' y'} @ ghost @@ total
  end) : sig
    val apply : t -> t -> F.result @ ghost @@ total
    val beta : (x : E.t) -> (y : E.t) ->
      {u : unit | apply (class_of x) (class_of y) === F.f x y}
      @ ghost @@ total
  end

  (** Prove a predicate for every class by proving it for every
      representative. This also applies to empty representative types. *)
  val induct : (q : t) -> (predicate : (t -> bool @ ghost)) @ total ->
    ((x : E.t) -> {u : unit | predicate (class_of x)} @ ghost) @ total ->
    {u : unit | predicate q} @ ghost @@ total
end
