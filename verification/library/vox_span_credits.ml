type (+'n : logical_data) token =
  { balance : 'n @@ ghost global total contended }

type (+'l : logical_data, +'r : logical_data) partition =
  { left : 'l token @@ ghost; right : 'r token @@ ghost }

let (credits @ total)
    (token : 'n token @ local immutable nonportable total ghost) :
    'n @ ghost = token.balance

let (tick @ total) (n : {n : Bigint.t | 0Z < n} @ ghost)
    (_token : {k : Bigint.t | k = n} token
      @ local unique nonportable total ghost) :
    {k : Bigint.t | k = Bigint.sub n 1Z} token
      @ unique nonportable total ghost =
  {balance = ghost_ (Bigint.sub n 1Z)}

let (split @ total) (left : {n : Bigint.t | 0Z <= n} @ ghost)
    (right : {n : Bigint.t | 0Z <= n} @ ghost)
    (_token : {n : Bigint.t | n = Bigint.add left right} token
      @ local unique nonportable total ghost) :
    ({n : Bigint.t | n = left}, {n : Bigint.t | n = right}) partition
      @ unique nonportable total =
  {left = {balance = left}; right = {balance = right}}

let (merge @ total) (left : {n : Bigint.t | 0Z <= n} @ ghost)
    (right : {n : Bigint.t | 0Z <= n} @ ghost)
    (_left : {n : Bigint.t | n = left} token
      @ local unique nonportable total ghost)
    (_right : {n : Bigint.t | n = right} token
      @ local unique nonportable total ghost) :
    {n : Bigint.t | n = Bigint.add left right} token
      @ unique nonportable total ghost =
  {balance = ghost_ (Bigint.add left right)}

(* Only scheduling is reclassified: callbacks are stateless, and no domain
   handle escapes. Scheduling remains partial; the cast itself is total. *)
external stateless_scheduler :
  ((unit -> 'a @ portable) @ portable once stateless ->
   (unit -> 'b @ portable) @ portable once stateless ->
   'a * 'b @ portable) ->
  ((unit -> 'a @ portable) @ portable once stateless ->
   (unit -> 'b @ portable) @ portable once stateless ->
   'a * 'b @ portable) @ stateless @@ total = "%identity"

type 'a result = { value : 'a @@ aliased portable }

let schedule
    (left : (unit -> 'a @ portable) @ portable once stateless)
    (right : (unit -> 'b @ portable) @ portable once stateless) :
    'a * 'b @ portable =
  let l, r = Vox_parallel.fork_join
    (fun () -> {value = left ()})
    (fun () -> {value = right ()}) in
  l.value, r.value

let schedule = stateless_scheduler schedule

let (fork_join @ stateless) (n : {n : Bigint.t | 0Z <= n} @ ghost)
    (_token : {k : Bigint.t | k = n} token
      @ local unique nonportable total ghost)
    (left : ({k : Bigint.t | k = n} token
      @ local unique nonportable total ghost -> 'a @ portable)
        @ portable once stateless)
    (right : ({k : Bigint.t | k = n} token
      @ local unique nonportable total ghost -> 'b @ portable)
        @ portable once stateless) : 'a * 'b @ portable =
  schedule
    (fun () -> left {balance = n})
    (fun () -> right {balance = n})

let run (n : {n : Bigint.t | 0Z <= n} @ ghost)
    (body : ({k : Bigint.t | k = n} token
      @ local unique nonportable total ghost -> 'a @ portable)
        @ portable once stateless) : 'a @ portable =
  body {balance = n}
