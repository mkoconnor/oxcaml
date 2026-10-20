@@ portable

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

module Make () : sig
  include S
  module Budget : sig
    val create : (amount : {n : Q.t | Q.nonnegative n}) @ ghost ->
      {t : token | credits t === amount}
        @ unique total ghost @@ total
  end
end
