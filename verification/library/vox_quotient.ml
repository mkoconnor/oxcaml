module Make (E : sig @@ portable include Map.EquatableType end) = struct
  module M = Map.MakeLogical (E)
  type t = {m : unit M.t | M.cardinal m = 1Z}

  let[@def] (class_of @ total) (x : E.t) : t @ ghost =
    ghost_ (M.add x () (M.empty ()))

  let (class_equal @ total) (x : E.t) (y : E.t) :
      {u : unit | (class_of x === class_of y) = E.equal x y}
      @ ghost = ghost_ (
    class_of_def x; class_of_def y;
    let _ = M.find_opt x (class_of x) in
    let _ = M.find_opt x (class_of y) in
    ())

  let (zero_empty @ total) (m : {m : unit M.t | M.cardinal m = 0Z}) :
      {u : unit | m === M.empty ()} @ ghost = ghost_ (
    match M.Proof.difference m (M.empty ()) with
    | None -> ()
    | Some x -> let _ = M.cardinal (M.remove x m) in ())

  let (representative @ total) (q : t) :
      {x : E.t | class_of x === q} @ ghost = ghost_ (
    match M.Proof.difference q (M.empty ()) with
    | None -> unreachable_ ()
    | Some x ->
      class_of_def x;
      let rest = M.remove x q in
      zero_empty rest;
      x)

  module Lift (F : sig @@ portable
    type result : logical_data
    val f : E.t -> result @ ghost @@ total
    val respects : (x : E.t) -> (y : E.t) ->
      {u : unit | not (E.equal x y) || f x === f y} @ ghost @@ total
  end) = struct
    let[@def] (apply @ total) (q : t) : F.result @ ghost =
      ghost_ (F.f (representative q))
    let (beta @ total) (x : E.t) :
        {u : unit | apply (class_of x) === F.f x} @ ghost = ghost_ (
      let y = representative (class_of x) in
      class_equal y x;
      F.respects y x;
      apply_def (class_of x);
      ())
  end

  module Lift2 (F : sig @@ portable
    type result : logical_data
    val f : E.t -> E.t -> result @ ghost @@ total
    val respects : (x : E.t) -> (x' : E.t) ->
      (y : E.t) -> (y' : E.t) ->
      {u : unit | not (E.equal x x' && E.equal y y') ||
        f x y === f x' y'} @ ghost @@ total
  end) = struct
    let[@def] (apply @ total) (x : t) (y : t) : F.result @ ghost =
      ghost_ (F.f (representative x) (representative y))
    let (beta @ total) (x : E.t) (y : E.t) :
        {u : unit | apply (class_of x) (class_of y) === F.f x y}
        @ ghost = ghost_ (
      let x' = representative (class_of x) in
      let y' = representative (class_of y) in
      class_equal x' x; class_equal y' y;
      F.respects x' x y' y;
      apply_def (class_of x) (class_of y);
      ())
  end

  let (induct @ total) (q : t)
      (predicate : (t -> bool @ ghost) @ total)
      (case : ((x : E.t) ->
        {u : unit | predicate (class_of x)} @ ghost) @ total) :
      {u : unit | predicate q} @ ghost = ghost_ (
    case (representative q))
end
