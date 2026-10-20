(* TEST
 include ocamlcommon;
 expect;
*)

let () =
  Compmisc.init_path ();
  let loc = Location.none in
  let parse env source =
    let _, _, _, _, _, env =
      Typemod.type_structure env
        (Parse.implementation (Lexing.from_string source))
    in
    env
  in
  let ident name = Longident.Lident name in
  let dot parent name =
    Longident.Ldot (Location.mknoloc parent, Location.mknoloc name)
  in
  let apply fn arg =
    Longident.Lapply (Location.mknoloc fn, Location.mknoloc arg)
  in
  let check_value ~locked env lid =
    let path, _, (_, named) = Env.lookup_value ~loc lid env in
    let resolved, _, (_, locks) = Env.lookup_value_path ~loc path env in
    assert (Path.same path resolved);
    assert (Env.locks_is_empty named = not locked);
    assert (Env.locks_is_empty locks = not locked);
    path
  in
  let check_constructor ~locked env lid path =
    let _, named = Env.lookup_constructor ~loc Env.Positive lid env in
    let _, locks =
      Env.lookup_constructor_path ~loc Env.Positive path env
    in
    assert (Env.locks_is_empty named = not locked);
    assert (Env.locks_is_empty locks = not locked)
  in
  let rejects predicate f =
    match f () with
    | _ -> failwith "Lookup unexpectedly succeeded"
    | exception Env.Error (Env.Lookup_error (_, _, error)) ->
        assert (predicate error)
  in
  let env = parse (Lazy.force Env.initial) {|
    let value = 0
    module M = struct
      let f x = x
      exception E
      module N = struct let f x = x exception E end
    end
    module F (X : sig end) = struct let f x = x exception E end
    module A = struct end
  |} in
  let region = Env.add_region_lock env in
  let original, md, (_, locks) =
    Env.lookup_module ~loc (ident "M") region
  in
  let alias = Ident.create_local "Alias" in
  let alias_path = Path.Pident alias in
  let md = { md with Types.md_type = Types.Mty_alias original } in
  let aliased =
    Env.add_module_declaration ~check:false alias Types.Mp_absent md
      ~locks region
  in
  let saved = check_value ~locked:true aliased (dot (ident "Alias") "f") in
  check_constructor ~locked:true aliased (dot (ident "Alias") "E")
    (Path.Pdot (alias_path, "E"));
  ignore (check_value ~locked:true aliased
    (dot (dot (ident "Alias") "N") "f"));
  check_constructor ~locked:true aliased
    (dot (dot (ident "Alias") "N") "E")
    (Path.Pdot (Path.Pdot (alias_path, "N"), "E"));
  let shadowed =
    Env.add_module (Ident.create_local "Alias") Types.Mp_present
      (Types.Mty_signature []) aliased
  in
  let resolved, _, (_, locks) =
    Env.lookup_value_path ~loc saved shadowed
  in
  assert (Path.same saved resolved);
  assert (not (Env.locks_is_empty locks));
  let application = apply (ident "F") (ident "A") in
  let applied_path, _, _ = Env.lookup_module ~loc application region in
  ignore (check_value ~locked:false region (dot application "f"));
  check_constructor ~locked:false region (dot application "E")
    (Path.Pdot (applied_path, "E"));
  ignore (check_value ~locked:true (Env.enter_quote region)
    (dot (ident "Stdlib") "ignore"));
  let stage_error = function
    | Env.Incompatible_stage _ -> true
    | _ -> false
  in
  let quoted = Env.enter_quote env in
  let value_path, value, (mode, _) =
    Env.lookup_value ~loc (ident "value") env
  in
  rejects stage_error
    (fun () -> Env.lookup_value ~loc (ident "value") quoted);
  rejects stage_error
    (fun () -> Env.lookup_value_path ~loc value_path quoted);
  let _, functor_md, _ = Env.lookup_module ~loc (ident "F") env in
  let inside = Ident.create_local "Inside" in
  let quoted =
    Env.add_module inside Types.Mp_present functor_md.Types.md_type quoted
  in
  let argument, _, _ = Env.lookup_module ~loc (ident "A") env in
  let application = apply (ident "Inside") (ident "A") in
  let applied_path = Path.Papply (Path.Pident inside, argument) in
  rejects stage_error
    (fun () -> Env.lookup_value ~loc (dot application "f") quoted);
  rejects stage_error
    (fun () ->
      Env.lookup_value_path ~loc (Path.Pdot (applied_path, "f")) quoted);
  rejects stage_error
    (fun () ->
      Env.lookup_constructor ~loc Env.Positive (dot application "E") quoted);
  rejects stage_error
    (fun () ->
      Env.lookup_constructor_path ~loc Env.Positive
        (Path.Pdot (applied_path, "E")) quoted);
  let mutable_id = Ident.create_local "mutable_value" in
  let value =
    { value with Types.val_kind =
        Types.Val_mut (Mode.Value.Comonadic.newvar (),
          Jkind_types.Sort.Base Scannable) }
  in
  let mutable_env =
    Env.add_value ~mode mutable_id value env
    |> Env.add_const_closure_lock (loc, Mode.Hint.Function)
         Mode.Value.Comonadic.Const.legacy
  in
  let mutable_error = function
    | Env.Mutable_value_used_in_closure _ -> true
    | _ -> false
  in
  rejects mutable_error
    (fun () -> Env.lookup_value ~loc (ident "mutable_value") mutable_env);
  rejects mutable_error
    (fun () ->
      Env.lookup_value_path ~loc (Path.Pident mutable_id) mutable_env)
;;
[%%expect{|
|}]
