@@ portable

(** Affine span credits. The type parameter describes the balance; the
    token itself is nonportable, including when stored in a ghost field.
    Observe the balance with [credits] before using it in a refinement.
    A fully specified coercion can weaken the balance refinement. *)
type (+'n : logical_data) token : void mod logical

type (+'l : logical_data, +'r : logical_data) partition =
  { left : 'l token @@ ghost; right : 'r token @@ ghost }

val credits : 'n token @ local immutable nonportable total ghost ->
  'n @ ghost @@ total

val tick : (n : {n : Bigint.t | 0Z < n}) @ ghost ->
  {k : Bigint.t | k = n} token
    @ local unique nonportable total ghost ->
  {k : Bigint.t | k = Bigint.sub n 1Z} token
    @ unique nonportable total ghost @@ total

val split : (left : {n : Bigint.t | 0Z <= n}) @ ghost ->
  (right : {n : Bigint.t | 0Z <= n}) @ ghost ->
  {n : Bigint.t | n = Bigint.add left right} token
    @ local unique nonportable total ghost ->
  ({n : Bigint.t | n = left}, {n : Bigint.t | n = right}) partition
    @ unique nonportable total @@ total

val merge : (left : {n : Bigint.t | 0Z <= n}) @ ghost ->
  (right : {n : Bigint.t | 0Z <= n}) @ ghost ->
  {n : Bigint.t | n = left} token
    @ local unique nonportable total ghost ->
  {n : Bigint.t | n = right} token
    @ local unique nonportable total ghost ->
  {n : Bigint.t | n = Bigint.add left right} token
    @ unique nonportable total ghost @@ total

(** Consumes the fork budget and supplies it to each branch. Branch
    leftovers are discarded. Reserve continuation credits with [split]
    before forking. Portable callbacks cannot capture those credits;
    portable results cannot return branch credits, even in a closure or
    ghost field. Stateless callbacks exclude shared-state synchronization.
    Both branches finish before return; exceptions follow
    [Vox_parallel.fork_join]. Nested calls are allowed. *)
val fork_join : (n : {n : Bigint.t | 0Z <= n}) @ ghost ->
  {k : Bigint.t | k = n} token
    @ local unique nonportable total ghost ->
  ({k : Bigint.t | k = n} token
    @ local unique nonportable total ghost -> 'a @ portable)
      @ portable once stateless ->
  ({k : Bigint.t | k = n} token
    @ local unique nonportable total ghost -> 'b @ portable)
      @ portable once stateless ->
  'a * 'b @ portable @@ stateless

(** Introduces the initial span budget. The body may call [tick], [split],
    [merge], and [fork_join], but cannot nest [run] or export span credits.
    Work credits from [Vox_big_credits] may be supplied separately.

    The budget bounds the longest dependency chain of charged [tick] events
    on normally returning executions. Instructions between ticks and
    scheduler overhead are uncharged; termination is not established.
    The semantic argument uses affine consumption, additive splitting and
    merging, and duplication only across isolated fork branches. It trusts
    the private stateless scheduling contract and the compiler's mode and
    erasure checks; it is not a mechanized compiler adequacy theorem. *)
val run : (n : {n : Bigint.t | 0Z <= n}) @ ghost ->
  ({k : Bigint.t | k = n} token
    @ local unique nonportable total ghost -> 'a @ portable)
      @ portable once stateless ->
  'a @ portable
