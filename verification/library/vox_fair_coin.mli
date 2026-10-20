module Q = Vox_real
module C = Vox_probability.Cost

(** Repeats fresh fair-coin draws until zero, charging one credit per draw.
    Each continuation receives two credits; each exit receives zero.
    Under [Vox_probability]'s assumptions, survival after n draws is 2^-n
    and the expected number of draws is two. [Vox_geometric_cost] proves
    the finite-prefix recurrence and its limit. This function is partial:
    the infinite sequence of continuation outcomes has probability zero,
    but is still an execution, so ordinary totality does not apply. *)
val retry :
  {t : C.token | Q.le (Q.of_bigint 2Z) (C.credits t)}
    @ unique total ghost -> unit
