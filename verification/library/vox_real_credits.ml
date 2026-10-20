module Q = Vox_real

module type S = sig
  type token : void mod logical

  type partition = { left : token @@ ghost; right : token @@ ghost }

  val credits : token @ local immutable total ghost -> Q.t @ ghost @@ total

  val nonnegative : (token : token) @ local immutable total ghost ->
    {u : unit | Q.nonnegative (credits token)} @ ghost @@ total

  val empty : unit -> {t : token | credits t === Q.of_bigint 0Z}
    @ unique total ghost @@ total

  val tick : (token : {t : token | Q.le (Q.of_bigint 1Z) (credits t)})
      @ unique total ghost ->
    {t : token |
      credits t === Q.sub (credits token) (Q.of_bigint 1Z)}
      @ unique total ghost @@ total

  val split : (amount : Q.t) @ ghost ->
    (token : {t : token | Q.nonnegative amount && Q.le amount (credits t)})
      @ unique total ghost ->
    {p : partition | credits p.left === amount &&
      credits p.right === Q.sub (credits token) amount} @ unique @@ total

  val merge : (left : token) @ unique total ghost ->
    (right : token) @ unique total ghost ->
    {t : token |
      credits t === Q.add (credits left) (credits right)}
      @ unique total ghost @@ total

end

module Make () = struct
  type amount = {n : Q.t | Q.nonnegative n}
  type token = { balance : amount @@ ghost global total contended }
  type partition = { left : token @@ ghost; right : token @@ ghost }

  let[@def] credits (token : token @ local immutable total ghost) =
    ghost_ (token.balance)

  let (nonnegative @ total) (token : token @ local immutable total ghost) :
      {u : unit | Q.nonnegative (credits token)} @ ghost = ghost_ (
    credits_def token;
    let _ = token.balance in
    ())

  let (tick @ total) (token : {t : token | Q.le (Q.of_bigint 1Z) (credits t)}
        @ unique total ghost) :
      {t : token |
      credits t === Q.sub (credits token) (Q.of_bigint 1Z)}
      @ unique total ghost =
    ghost_ (credits_def (borrow_ token));
    let result = { balance = ghost_ (
      let balance = token.balance in
      let n = Q.sub balance (Q.of_bigint 1Z) in (n : amount)) } in
    ghost_ (credits_def token; credits_def (borrow_ result));
    result

  let (split @ total) (amount : Q.t @ ghost)
      (token : {t : token | Q.nonnegative amount && Q.le amount (credits t)}
        @ unique total ghost) :
      {p : partition | credits p.left === amount &&
        credits p.right === Q.sub (credits token) amount} @ unique =
    let left = { balance = ghost_ (amount : amount) } in
    ghost_ (credits_def (borrow_ token));
    let right = { balance = ghost_ (
      let balance = token.balance in
      let n = Q.sub balance amount in (n : amount)) } in
    let result = { left; right } in
    ghost_ (credits_def token; credits_def (borrow_ result.left);
      credits_def (borrow_ result.right));
    result

  let (merge @ total) (left : token @ unique total ghost)
      (right : token @ unique total ghost) :
      {t : token |
      credits t === Q.add (credits left) (credits right)}
      @ unique total ghost =
    ghost_ (credits_def (borrow_ left); credits_def (borrow_ right));
    let result = { balance = ghost_ (
      let a = left.balance in
      let b = right.balance in
      let n = Q.add a b in (n : amount)) } in
    ghost_ (credits_def (borrow_ result));
    result

  module Budget = struct
    let (create @ total) (amount : {n : Q.t | Q.nonnegative n} @ ghost) :
        {t : token | credits t === amount}
        @ unique total ghost =
      let result = { balance = ghost_ (amount : amount) } in
      ghost_ (credits_def (borrow_ result));
      result
  end
  let (empty @ total) () :
      {t : token | credits t === Q.of_bigint 0Z} @ unique total ghost =
    Budget.create (ghost_ (Q.of_bigint 0Z))
end
