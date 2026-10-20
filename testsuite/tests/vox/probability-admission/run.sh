#!/bin/sh
set -eu
compiler=$1
stdlib=$2
extension=$3
library="$PWD/prebuilt"
source_library=$(cd "$(dirname "$0")/../../../../verification/library" && pwd)
VOX_VERIFY_CACHE=
export VOX_VERIFY_CACHE
rm -rf work
mkdir work
cd work
compile() {
  "$compiler" -nostdlib -I "$stdlib" -I "$library" \
    -extension refinement_types "$@"
}
objects=""
for unit in vox_sequence vox_real \
    vox_real_credits vox_expectation vox_probability; do
  objects="$objects $library/$unit.$extension"
done
link() {
  # The list contains generated paths without whitespace.
  compile -vox-probabilistic $objects "$@" -o program
}
reject() {
  expected=$1
  shift
  if link "$@" > rejected.log 2>&1; then
    echo "unexpected admission: $*"
    exit 1
  fi
  if ! grep -F "$expected" rejected.log > /dev/null; then
    cat rejected.log
    exit 1
  fi
}
cat > prefix <<'ML'
module Q = Vox_real
module P = Vox_probability
ML
cat > body <<'ML'
  let zero = ghost_ (Q.of_bigint 0Z) in
  P.run zero zero (fun _cost _error _monitor -> ())
ML
{ cat prefix; echo 'let () ='; cat body; } > root.ml
compile -c root.ml
link "root.$extension"
./program
for fixture in opened local_open nested_open; do
  cat prefix > "$fixture.ml"
  case "$fixture" in
    opened)
      echo 'open Vox_probability' >> "$fixture.ml"
      echo 'let () =' >> "$fixture.ml"
      sed 's/P.run/run/' body >> "$fixture.ml" ;;
    local_open)
      echo 'let () = let open Vox_probability in' >> "$fixture.ml"
      sed 's/P.run/run/' body >> "$fixture.ml" ;;
    nested_open)
      echo 'module H = struct module P = Vox_probability end' >> "$fixture.ml"
      echo 'open H' >> "$fixture.ml"
      echo 'let () =' >> "$fixture.ml"
      cat body >> "$fixture.ml" ;;
  esac
  compile -c "$fixture.ml"
  if ! link "$fixture.$extension" > admitted.log 2>&1; then
    cat admitted.log
    exit 1
  fi
  ./program
done
echo 'module opens admitted'
: > empty.manifest
reject 'custom runtime or linker inputs are unsupported' \
  -I-manifest empty.manifest "root.$extension"
reject 'custom runtime or linker inputs are unsupported' \
  -H-manifest empty.manifest "root.$extension"
if [ "$extension" = cmx ]; then
  reject 'cached generic-function objects are unsupported' \
    -use-cached-generic-functions \
    -cached-generic-functions-path root.o root.cmx
fi
echo 'custom linker inputs rejected'
reject 'expected one initial credit root, found 0'
echo 'missing root rejected'
cp root.ml second.ml
compile -c second.ml
reject 'expected one initial credit root, found 2' \
  "root.$extension" "second.$extension"
echo 'separate roots rejected'
for fixture in nested lazy loop functor letop list_comp array_comp; do
  cat prefix > "$fixture.ml"
  case "$fixture" in
    nested) echo 'let again () =' >> "$fixture.ml"; cat body >> "$fixture.ml" ;;
    lazy) echo 'let again = lazy (' >> "$fixture.ml";
      cat body >> "$fixture.ml"; echo ')' >> "$fixture.ml" ;;
    loop) echo 'let () = for i = 1 to 2 do' >> "$fixture.ml";
      cat body >> "$fixture.ml"; echo 'done' >> "$fixture.ml" ;;
    functor) echo 'module F () = struct let () =' >> "$fixture.ml";
      cat body >> "$fixture.ml"; echo 'end' >> "$fixture.ml" ;;
    letop) echo 'let (let*) () f = f (); f ()' >> "$fixture.ml";
      echo 'let () = let* () = () in' >> "$fixture.ml";
      cat body >> "$fixture.ml" ;;
    list_comp) echo 'let _ = [' >> "$fixture.ml";
      cat body >> "$fixture.ml"; echo 'for _i = 1 to 2]' >> "$fixture.ml" ;;
    array_comp) echo 'let _ = [|' >> "$fixture.ml";
      cat body >> "$fixture.ml"; echo 'for _i = 1 to 2|]' >> "$fixture.ml" ;;
  esac
  compile -extension comprehensions -c "$fixture.ml"
  reject 'credit root must be applied in initialization' \
    "$fixture.$extension" "root.$extension"
done
echo 'val value : int' > parameter.mli
compile -as-parameter -c parameter.mli
{ echo 'let observed = Parameter.value'; cat root.ml; } > parameterized.ml
compile -parameter Parameter -c parameterized.ml
reject 'Parameterized is not an ordinary compilation unit' \
  "parameterized.$extension" "root.$extension"
echo 'repeated initialization rejected'
{ cat prefix; echo 'let issue = P.run'; } > alias.ml
compile -c alias.ml
reject 'credit root escapes initialization' "alias.$extension" "root.$extension"
echo 'root alias rejected'
cat > hidden.mli <<'ML'
val value : int
ML
{ cat nested.ml; echo 'let value = 0'; } > hidden.ml
compile -c hidden.mli
compile -c hidden.ml
reject 'credit root must be applied in initialization' \
  "hidden.$extension" "root.$extension"
echo 'hidden root rejected'
for fixture in hidden_alias preserved_alias; do
  echo 'val value : int' > "$fixture.mli"
  echo 'module Q = Vox_real' > "$fixture.ml"
  if [ "$fixture" = hidden_alias ]; then
    echo 'module H = struct module P = Vox_probability end' >> "$fixture.ml"
  else
    cat >> "$fixture.ml" <<'ML'
module H : sig module P = Vox_probability end =
  struct module P = Vox_probability end
ML
  fi
  cat >> "$fixture.ml" <<'ML'
let value =
  let zero = ghost_ (Q.of_bigint 0Z) in
  H.P.run zero zero (fun _cost _error _monitor -> 0)
ML
  compile -c "$fixture.mli"
  compile -c "$fixture.ml"
  if ! link "$fixture.$extension" > admitted.log 2>&1; then
    cat admitted.log
    exit 1
  fi
  ./program
done
echo 'hidden aliases admitted'
cat > sealed.mli <<'ML'
module P : module type of Vox_probability
ML
cat > sealed.ml <<'ML'
module P = Vox_probability
ML
compile -c sealed.mli
compile -c sealed.ml
reject 'credit root module is sealed by interface' \
  "sealed.$extension" "root.$extension"
echo 'val value : int' > hidden_sealed.mli
cat > hidden_sealed.ml <<'ML'
module Q = Vox_real
module H : sig
  module P : sig
    val run : (cost : {q : Q.t | Q.nonnegative q}) @ ghost ->
      (error : {q : Q.t | Q.nonnegative q}) @ ghost ->
      ((cost : {t : Vox_probability.Cost.token |
          Vox_probability.Cost.credits t === cost}) @ unique total ghost ->
       (error : {t : Vox_probability.Error.token |
          Vox_probability.Error.credits t === error}) @ unique total ghost ->
       {m : Vox_probability.monitor | not (Vox_probability.failed m)}
          @ unique total ghost -> 'a) @ local once -> 'a
  end
end = struct module P = Vox_probability end
let again () =
  let zero = ghost_ (Q.of_bigint 0Z) in
  H.P.run zero zero (fun _cost _error _monitor -> ())
let value = again (); again (); 0
ML
compile -c hidden_sealed.mli
compile -c hidden_sealed.ml
reject 'credit root module is sealed by interface' \
  "hidden_sealed.$extension" "root.$extension"
cat > indirect.mli <<'ML'
module B : sig module P : module type of Vox_probability end
ML
cat > indirect.ml <<'ML'
module A = struct module P = Vox_probability end
module B = A
ML
compile -c indirect.mli
compile -c indirect.ml
reject 'module contains an escaping credit root' \
  "indirect.$extension" "root.$extension"
echo 'sealed root module rejected'
cat > anonymous_argument.ml <<'ML'
module Q = Vox_real
module F (X : sig
  module P : sig
    val run : (cost : {q : Q.t | Q.nonnegative q}) @ ghost ->
      (error : {q : Q.t | Q.nonnegative q}) @ ghost ->
      ((cost : {t : Vox_probability.Cost.token |
          Vox_probability.Cost.credits t === cost}) @ unique total ghost ->
       (error : {t : Vox_probability.Error.token |
          Vox_probability.Error.credits t === error}) @ unique total ghost ->
       {m : Vox_probability.monitor | not (Vox_probability.failed m)}
          @ unique total ghost -> 'a) @ local once -> 'a
  end
end) = struct
  let again () =
    let zero = ghost_ (Q.of_bigint 0Z) in
    X.P.run zero zero (fun _cost _error _monitor -> ())
end
module M = F(struct module P = Vox_probability end)
let () = M.again (); M.again ()
ML
compile -c anonymous_argument.ml
reject 'credit root module is passed to a functor' \
  "anonymous_argument.$extension" "root.$extension"
echo 'anonymous functor root rejected'
cat > prophecy.mli <<'ML'
val value : int
ML
cat > prophecy.ml <<'ML'
let[@def] (allocation @ total) (s : int Borrow.Slice.t @ local immutable) =
  ghost_ (match Borrow.Slice.final s with
    | [] -> [Vox_real.of_bigint 0Z; Vox_real.of_bigint 2Z]
    | _ -> [Vox_real.of_bigint 2Z; Vox_real.of_bigint 0Z])
let value = 0
ML
compile -c prophecy.mli
compile -c prophecy.ml
reject 'Borrow' "prophecy.$extension" "root.$extension"
echo 'hidden prophecy rejected'
echo 'let value = 0' > skipped.ml
compile -smt-assume-verified -c skipped.ml
reject 'Skipped was not verified' "skipped.$extension" "root.$extension"
echo 'let value = 0' > unrecorded.ml
"$compiler" -nostdlib -I "$stdlib" -c unrecorded.ml
reject 'Unrecorded has no verification record' \
  "unrecorded.$extension" "root.$extension"
echo 'skipped verification rejected'
cat > trusted.ml <<'ML'
external pretend : unit -> unit @@ total = "%identity"
ML
compile -vox-library -c trusted.ml
reject 'Trusted uses pretend' "trusted.$extension" "root.$extension"
echo 'unapproved library assumption rejected'
cat > proof_axiom.mli <<'ML'
external bogus : unit -> {u : unit | false} @@ total = "%identity"
ML
cp proof_axiom.mli proof_axiom.ml
compile -vox-library -c proof_axiom.mli
compile -vox-library -c proof_axiom.ml
cat > proof.mli <<'ML'
val value : int
ML
cat > proof.ml <<'ML'
let value = ghost_ (Proof_axiom.bogus ()); 0
ML
compile -c proof.mli
compile -c proof.ml
reject 'Proof_axiom uses bogus' "proof.$extension" "root.$extension"
echo 'erased implementation dependency rejected'
echo 'let value = 1' > helper.ml
compile -c helper.ml
echo 'let value = Helper.value' > client.ml
compile -c client.ml
echo 'let value = true' > helper.ml
compile -c helper.ml
reject 'Helper has a mismatched interface digest' \
  "helper.$extension" "client.$extension" "root.$extension"
echo 'stale interface rejected'
if [ "$extension" = cmx ]; then archive=cmxa; else archive=cma; fi
compile -a "helper.$extension" -o helper_archive.$archive
reject 'only loose' "helper_archive.$archive" "root.$extension"
echo 'let value = 0' > pack_member.ml
if [ "$extension" = cmx ]; then
  compile -for-pack Packed -c pack_member.ml
else
  compile -c pack_member.ml
fi
compile -pack "pack_member.$extension" -o "packed.$extension"
reject 'Packed has no current admission record' \
  "packed.$extension" "root.$extension"
cp "helper_archive.$archive" "stdlib.$archive"
reject 'differs from the installed runtime' "root.$extension"
rm "stdlib.$archive"
if [ "$extension" = cmo ]; then
  printf 'sh\n/unapproved/runtime\000\n' > runtime-launch-info
  reject 'runtime-launch-info differs from the installed runtime' root.cmo
  rm runtime-launch-info
fi
echo 'archive and runtime substitution rejected'
echo 'let reset () = Random.init 42' > reset.ml
compile -c reset.ml
reject 'Stdlib__Random' "reset.$extension" "root.$extension"
cat > stdlib_alias.mli <<'ML'
module S : sig module Random : sig val init : int -> unit end end
ML
cat > stdlib_alias.ml <<'ML'
module S = Stdlib
ML
compile -c stdlib_alias.mli
compile -c stdlib_alias.ml
reject 'standard library module escapes' \
  "stdlib_alias.$extension" "root.$extension"
cat > array_alias.mli <<'ML'
module A : sig val unsafe_get : 'a array -> int -> 'a end
ML
cat > array_alias.ml <<'ML'
module A = Array
ML
compile -c array_alias.mli
compile -c array_alias.ml
reject 'module exposes unsafe capabilities' \
  "array_alias.$extension" "root.$extension"
echo 'random state access rejected'
mkdir fake
cd fake
echo 'let harmless = 0' > vox_probability.ml
compile -vox-library -c vox_probability.ml
if compile -vox-probabilistic "vox_probability.$extension" -o fake \
    > rejected.log 2>&1; then
  echo 'counterfeit kernel admitted'
  exit 1
fi
grep -F 'not the reviewed kernel source' rejected.log > /dev/null
echo 'let harmless = 0' > vox_real.ml
compile -vox-library -c vox_real.ml
if compile -vox-probabilistic "vox_real.$extension" -o fake \
    > rejected.log 2>&1; then
  echo 'counterfeit arithmetic admitted'
  exit 1
fi
grep -F 'not the reviewed kernel source' rejected.log > /dev/null
echo 'let harmless = 0' > stdlib__List.ml
compile -nopervasives -c stdlib__List.ml
if compile -vox-probabilistic "stdlib__List.$extension" -o fake \
    > rejected.log 2>&1; then
  echo 'counterfeit runtime interface admitted'
  exit 1
fi
grep -F 'differs from the installed runtime' rejected.log > /dev/null
cd ..
for kernel in vox_probability vox_real vox_real_credits; do
  mkdir "inferred_$kernel"
  cd "inferred_$kernel"
  cp "$source_library/$kernel.ml" .
  compile -vox-library -c "$kernel.ml"
  if compile -vox-probabilistic "$kernel.$extension" -o fake \
      > rejected.log 2>&1; then
    echo "kernel with inferred interface admitted: $kernel"
    exit 1
  fi
  grep -F 'requires its reviewed explicit interface' rejected.log > /dev/null
  cd ..
done
echo 'inferred kernel interface rejected'
mkdir rebound
cp "$source_library/vox_probability.ml" \
  "$source_library/vox_probability.mli" root.ml rebound/
cd rebound
cat > evil.ml <<'ML'
module Random = struct let full_int _ = 0 end
ML
compile -c evil.ml
compile -vox-library -open Evil -c vox_probability.mli
compile -vox-library -open Evil -c vox_probability.ml
compile -c root.ml
original_objects=$objects
objects=""
for unit in vox_sequence vox_real \
    vox_real_credits vox_expectation; do
  objects="$objects $library/$unit.$extension"
done
objects="$objects evil.$extension vox_probability.$extension"
reject 'Vox_probability used unsupported kernel compilation options' \
  "root.$extension"
objects=$original_objects
cd ..
echo 'counterfeit kernel rejected'
if [ "$extension" = cmx ]; then
  echo 'val value : int' > native_helper.mli
  echo 'let value = 1' > native_helper.ml
  compile -c native_helper.mli
  compile -c native_helper.ml
  echo 'let value = Native_helper.value' > native_client.ml
  compile -c native_client.ml
  echo 'let value = 2' > native_helper.ml
  compile -c native_helper.ml
  reject 'Native_helper has a mismatched native digest' \
    native_helper.cmx native_client.cmx root.cmx
  cp root.o second.o
  reject 'Second has no matching native object' \
    "second.$extension" "root.$extension"
fi
echo 'artifact checks passed'
