module Q = Vox_real
module S = Vox_sequence
module E = Vox_expectation
module P = Vox_probability
module C = P.Cost

let (pair_facts @ total) (left : Q.t) (right : Q.t) (index : int) :
    {u : unit | S.length [left; right] = 2Z &&
      (if Q.nonnegative left && Q.nonnegative right then
        Q.all_nonnegative [left; right] else true) &&
      (if 0 <= index && index < 2 then
        E.entry [left; right] (Bigint.of_int index) ===
          (if index = 0 then left else right) else true)} @ ghost = ghost_ (
  S.length_def [left; right]; S.length_def [right]; S.length_def [];
  Q.all_nonnegative_def [left; right]; Q.all_nonnegative_def [right];
  Q.all_nonnegative_def [];
  E.entry_def [left; right] (Bigint.of_int index);
  S.at_def [left; right] (Bigint.of_int index);
  S.at_def [right] (Bigint.sub (Bigint.of_int index) 1Z);
  S.at_def [] (Bigint.sub (Bigint.of_int index) 2Z))

let (allocation @ total) () :
    {u : unit | Q.le (E.uniform [Q.of_bigint 0Z; Q.of_bigint 2Z])
      (Q.of_bigint 1Z) && Q.nonnegative (Q.of_bigint 0Z) &&
      Q.nonnegative (Q.of_bigint 2Z)} @ ghost = ghost_ (
  let zero = Q.of_bigint 0Z in
  let two = Q.of_bigint 2Z in
  E.uniform_pair zero two; E.pair_mean_def zero two)

let rec retry
    (cost : {t : C.token | Q.le (Q.of_bigint 2Z) (C.credits t)}
      @ unique total ghost) : unit =
  let zero = ghost_ (Q.of_bigint 0Z) in
  let two = ghost_ (Q.of_bigint 2Z) in
  let cost = C.tick cost in
  ghost_ (
    allocation (); pair_facts zero two 0);
  let #{P.index; cost} = P.uniform_cost 2 [zero; two] cost in
  if index = 0 then () else (
    ghost_ (pair_facts zero two index);
    retry cost)
