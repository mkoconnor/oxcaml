open Cmi_format

let imports_with_digests imports =
  List.map
    (fun import ->
      ( Compilation_unit.Name.to_string (Import_info.name import),
        Option.map Digest.to_hex (Import_info.crc import) ))
    imports

let recorded_import import =
  match String.index_opt import '=' with
  | Some i ->
    let digest = String.sub import (i + 1) (String.length import - i - 1) in
    String.sub import 0 i, (if digest = "" then None else Some digest)
  | None -> import, None

let read_cmi file =
  match Cmi_format.read_cmi_lazy file with
  | cmi ->
    Some
      ( Cmi_format.vox_unit cmi.cmi_flags,
        imports_with_digests (Array.to_list cmi.cmi_crcs) )
  | exception _ -> None

let with_magic file magic read =
  match
    In_channel.with_open_bin file (fun channel ->
        let found = really_input_string channel (String.length magic) in
        if String.equal found magic then Some (read channel) else None)
  with
  | result -> result
  | exception _ -> None

(* A .cmo ends with its compilation unit description, whose position follows
   the magic number, and then its Vox record. *)
let read_cmo file =
  with_magic file Config.cmo_magic_number (fun channel ->
      let position = input_binary_int channel in
      seek_in channel position;
      let unit = (input_value channel : Cmo_format.compilation_unit_descr) in
      ( Cmi_format.input_vox_record channel,
        imports_with_digests (Array.to_list unit.cu_imports) ))

(* A .cmx starts with its Vox record (see [Compilenv.write_unit_info]). *)
let read_cmx file =
  with_magic file Config.cmx_magic_number (fun channel ->
      let record = Cmi_format.input_vox_record channel in
      ( record,
        Option.fold ~none:[]
          ~some:(fun record -> List.map recorded_import record.vox_imports)
          record ))

let artifact target extension =
  Unit_info.Artifact.filename (Unit_info.artifact target ~extension)

(* The records that earlier compilations left in this unit's .cmo and .cmi. *)
let counterparts target () =
  List.filter_map Fun.id
    [ Option.bind (read_cmo (artifact target ".cmo")) fst;
      Option.bind (read_cmi (artifact target ".cmi")) fst ]

let find name extension =
  match Load_path.find_normalized (name ^ extension) with
  | file -> Some file
  | exception Not_found -> None

type unit_entry =
  { name : string;
    implementation : vox_unit option;
    interface : vox_unit option;
    unrecorded : string list;
        (** extensions of the unit's compiled files that have no record *)
    found : bool;  (** some compiled file of the unit was found *)
    digests : (string * string) list
        (** the interface digest recorded in each compiled file *)
  }

(* The .cmx and .cmo of a unit may come from different compilations; the
   weaker record counts, and the items of both. *)
let merge (a : vox_unit) (b : vox_unit) =
  { a with
    vox_status =
      (if a.vox_status = Vox_not_verified || b.vox_status = Vox_not_verified
       then Vox_not_verified
       else a.vox_status);
    vox_library = a.vox_library && b.vox_library;
    vox_solver =
      String.concat " "
        (List.sort_uniq String.compare
           (List.filter (fun s -> s <> "") [a.vox_solver; b.vox_solver]));
    vox_imports = List.sort_uniq String.compare (a.vox_imports @ b.vox_imports);
    vox_items = List.sort_uniq compare (a.vox_items @ b.vox_items) }

(* The units [name] depends on through its interface and implementation, and
   what their compiled files record. *)
let lookup name =
  let cmi = Option.bind (find name ".cmi") read_cmi in
  let cmx = Option.bind (find name ".cmx") read_cmx in
  let cmo = Option.bind (find name ".cmo") read_cmo in
  let interface = Option.bind cmi fst in
  let unrecorded =
    List.filter_map Fun.id
      [ (match cmx with Some (None, _) -> Some ".cmx" | _ -> None);
        (match cmo with Some (None, _) -> Some ".cmo" | _ -> None) ]
  in
  let implementation =
    match Option.bind cmx fst, Option.bind cmo fst with
    | Some a, Some b -> Some (merge a b)
    | (Some _ as record), None | None, (Some _ as record) -> record
    | None, None -> (
      (* A unit without an .mli: its .cmi has the implementation's record. *)
      match interface with
      | Some { vox_status = Vox_verified | Vox_not_verified; _ } -> interface
      | _ -> None)
  in
  let imports =
    Option.fold ~none:[] ~some:snd cmi
    @ Option.fold ~none:[] ~some:snd cmo
    @ Option.fold ~none:[] ~some:snd cmx
    @
    match implementation with
    | Some record -> List.map recorded_import record.vox_imports
    | None -> []
  in
  let digests =
    List.filter_map
      (fun (extension, artifact) ->
        Option.bind artifact (fun (_, imports) ->
            Option.map (fun digest -> extension, digest)
              (Option.join (List.assoc_opt name imports))))
      [".cmi", cmi; ".cmx", cmx; ".cmo", cmo]
  in
  ( { name;
      implementation;
      interface;
      unrecorded;
      digests;
      found = Option.is_some cmi || Option.is_some cmx || Option.is_some cmo },
    imports )

let closure ~current ~record ~imports =
  let seen = Hashtbl.create 64 in
  let current_entry =
    { name = current;
      implementation =
        (match record with
        | Some { vox_status = Vox_interface; _ } -> None
        | _ -> record);
      interface = record;
      unrecorded = [];
      digests = [];
      found = true }
  in
  Hashtbl.add seen current current_entry;
  let inconsistencies = ref [] in
  let check importer entry expected =
    match expected with
    | None -> ()
    | Some expected ->
      if entry.found && entry.name <> current && entry.digests = []
      then
        inconsistencies :=
          Printf.sprintf "%s (imported by %s; interface digest unavailable)"
            entry.name importer
          :: !inconsistencies;
      List.iter
        (fun (extension, actual) ->
          if expected <> actual
          then
            inconsistencies :=
              Printf.sprintf "%s (imported by %s; mismatched %s)"
                entry.name importer extension
              :: !inconsistencies)
        entry.digests
  in
  let rec visit acc = function
    | [] -> List.rev acc
    | (importer, (name, expected)) :: rest ->
      (match Hashtbl.find_opt seen name with
      | Some entry ->
        check importer entry expected;
        visit acc rest
      | None ->
        let entry, imports = lookup name in
        Hashtbl.add seen name entry;
        check importer entry expected;
        visit (entry :: acc)
          (rest @ List.map (fun import -> name, import) imports))
  in
  let entries =
    current_entry :: visit [] (List.map (fun import -> current, import) imports)
  in
  entries, List.sort_uniq String.compare !inconsistencies

let items entry =
  let all =
    Option.fold ~none:[] ~some:(fun r -> r.vox_items) entry.implementation
    @ Option.fold ~none:[] ~some:(fun r -> r.vox_items) entry.interface
  in
  let seen = Hashtbl.create 16 in
  List.filter
    (fun item ->
      let key = item.vox_kind, item.vox_name in
      if Hashtbl.mem seen key
      then false
      else begin
        Hashtbl.add seen key ();
        true
      end)
    all

let library entry =
  match entry.implementation, entry.interface with
  | Some r, _ | None, Some r -> r.vox_library
  | None, None -> false

let kinds =
  [ Vox_refined_external, "Externals whose refinement is assumed";
    Vox_total_external, "Externals assumed total";
    Vox_builtin, "Externals given a built-in meaning";
    Vox_total_cast, "Casts to total";
    Vox_cast_use, "Definitions that apply a cast to total";
    Vox_unsafe, "Unsafe features (Obj, Marshal, unsafe primitives, -unsafe)";
    Vox_external, "Other externals outside the library" ]

let print ppf ~source_file ~current ~record ~imports =
  let entries, inconsistencies = closure ~current ~record ~imports in
  let count = List.length entries - 1 in
  Format.fprintf ppf "Vox audit of %s and the %d unit%s it depends on@."
    source_file count
    (if count = 1 then "" else "s");
  let section title lines =
    if lines <> []
    then begin
      Format.fprintf ppf "@.%s:@." title;
      List.iter (fun line -> Format.fprintf ppf "  %s@." line) lines
    end
  in
  let units predicate =
    List.filter_map
      (fun entry -> if predicate entry then Some entry.name else None)
      entries
  in
  section "Verification skipped (-smt-assume-verified)"
    (units (fun entry ->
         match entry.implementation with
         | Some { vox_status = Vox_not_verified; _ } -> true
         | _ -> false));
  section "Verified with another solver (-smt-solver-any-version)"
    (List.filter_map
       (fun entry ->
         match entry.implementation with
         | Some { vox_solver; _ } when vox_solver <> "" ->
           Some (entry.name ^ ": " ^ vox_solver)
         | _ -> None)
       entries);
  section "Not compiled with refinement types (no Vox record)"
    (List.filter_map
       (fun entry ->
         if entry.found && entry.interface = None && entry.implementation = None
         then Some entry.name
         else if entry.unrecorded <> []
         then
           Some
             (Printf.sprintf "%s (its %s)" entry.name
                (String.concat " and " entry.unrecorded))
         else None)
       entries);
  section "Implementation record not found (no .cmx or .cmo)"
    (units (fun entry ->
         entry.implementation = None && entry.interface <> None));
  section "Compiled files not found"
    (units (fun entry -> not entry.found));
  section "Interface digest checks failed (audit incomplete)" inconsistencies;
  let total = ref 0 in
  List.iter
    (fun (kind, title) ->
      section title
        (List.concat_map
           (fun entry ->
             let items =
               List.filter (fun item -> item.vox_kind = kind) (items entry)
             in
             total := !total + List.length items;
             let counted item =
               if item.vox_count > 1
               then Printf.sprintf "%s x%d" item.vox_name item.vox_count
               else item.vox_name
             in
             if items = []
             then []
             else if library entry
             then
               (* The library's items are part of the trusted base; one line
                  per unit. *)
               [ Printf.sprintf "%s (library): %s" entry.name
                   (String.concat ", " (List.map counted items)) ]
             else
               List.map
                 (fun item ->
                   Printf.sprintf "%s%s"
                     (if kind = Vox_unsafe
                      then entry.name ^ ": " ^ counted item
                      else entry.name ^ "." ^ counted item)
                     (if item.vox_location = ""
                      then ""
                      else " (" ^ item.vox_location ^ ")"))
                 items)
           entries))
    kinds;
  Format.fprintf ppf "@.%d trusted item%s in total.@." !total
    (if !total = 1 then "" else "s")

let print_unit ~source_file ~current ~record =
  let imports =
    imports_with_digests (Env.imports ())
    @ Option.fold ~none:[]
        ~some:(fun record -> List.map recorded_import record.vox_imports)
        record
  in
  print Format.std_formatter ~source_file ~current ~record
    ~imports

type probability_object =
  { unit_name : string;
    ordinary : bool;
    record : vox_unit option;
    imports : (string * string option) list;
    native_imports : (string * string option) list;
    native_digest : string option }

let native_probability_object = ref (fun _ -> None)

let probability_error format =
  Printf.ksprintf
    (fun message ->
      Location.raise_errorf "Probabilistic admission: %s" message)
    format

let check_probability_options () =
  if !Vox_trust.probabilistic
  then begin
    if Clflags.(!make_archive || !make_package || !instantiate || !functorize
                || !shared || !output_c_object || !nopervasives)
    then probability_error "requires an ordinary executable link";
    if Clflags.(!ccobjs <> [] || !all_ccopts <> [] || !dllibs <> []
                || !dllpaths <> [] || !c_compiler <> None
                || !use_runtime <> "" || !use_prims <> ""
                || !runtime_variant <> "" || !custom_runtime
                || not !with_runtime
                || !include_manifests <> [] || !hidden_include_manifests <> []
                || !uses_metaprogramming || !requires_metaprogramming)
    then probability_error "custom runtime or linker inputs are unsupported"
  end

let byte_probability_object file =
  with_magic file Config.cmo_magic_number (fun channel ->
      let position = input_binary_int channel in
      seek_in channel position;
      let unit = (input_value channel : Cmo_format.compilation_unit_descr) in
      { unit_name = Compilation_unit.name_as_string unit.cu_name;
        ordinary = Compilation_unit.is_plain_name unit.cu_name
          && unit.cu_arg_descr = None
          && (match unit.cu_format with
              | Lambda.Mb_struct _ -> true
              | Lambda.Mb_instantiating_functor _ -> false);
        record = Cmi_format.input_vox_record channel;
        imports = imports_with_digests (Array.to_list unit.cu_imports);
        native_imports = [];
        native_digest = None })

(* Raw hashes of the reviewed kernel sources, admitted only without
   preprocessing. -vox-library does not confer approval. *)
let probability_kernel =
  [ ("Vox_probability",
     ("e1b716ff567bb92eaba50525b197ef26",
      Some "dd1646be8f149200e01185d6d052759a"));
    ("Vox_sequence",
     ("77f104870a4db3843489bd4ad549a332",
      Some "045bb8d6852673dc002bc02585879d00"));
    ("Vox_real",
     ("438145b8e8a0eb5c005ce6d03a8009f1",
      Some "bcf860db7016d25c1cbc6d9ab54ee239"));
    ("Vox_expectation",
     ("e0cea057b942b093403de21b6acd9f8d",
      None));
    ("Vox_real_credits",
     ("b94f2286decd308bb1a8c8e45f2b136c",
      Some "015bf1d267934ad64af8b34b9f31e4c5")) ]

let admit_probability ~native objfiles =
  if !Vox_trust.probabilistic
  then begin
    check_probability_options ();
    let extension = if native then ".cmx" else ".cmo" in
    let read = if native then !native_probability_object
      else byte_probability_object in
    let resolve file =
      match Load_path.find file with
      | file -> file
      | exception Not_found -> probability_error "cannot find %s" file
    in
    let digest file =
      match Digest.file file with
      | value -> Digest.to_hex value
      | exception Sys_error _ -> probability_error "cannot read %s" file
    in
    let same_installation_file file =
      let baseline = Filename.concat Config.standard_library_default
        (Filename.basename file) in
      Sys.file_exists baseline && digest file = digest baseline
    in
    let require_installation file =
      if not (same_installation_file file)
      then probability_error "%s differs from the installed runtime" file
    in
    let runtime_units =
      let file = Filename.concat Config.standard_library_default "stdlib.cma" in
      match with_magic file Config.cma_magic_number (fun channel ->
        let position = input_binary_int channel in
        seek_in channel position;
        let library = (input_value channel : Cmo_format.library) in
        List.map (fun unit -> Compilation_unit.name_as_string
          unit.Cmo_format.cu_name) library.lib_units) with
      | Some units -> units
      | None -> probability_error "cannot inspect the installed stdlib.cma"
    in
    let installed_interface name file =
      List.mem name runtime_units && same_installation_file file
    in
    let archive = resolve (if native then "stdlib.cmxa" else "stdlib.cma") in
    require_installation archive;
    if native then begin
      require_installation (Filename.remove_extension archive ^ Config.ext_lib);
      require_installation (resolve ("libasmrun" ^ Config.ext_lib))
    end else require_installation (resolve "runtime-launch-info");
    let selected = Hashtbl.create 32 in
    List.iter (fun requested ->
      if not (Filename.check_suffix requested extension)
      then probability_error "only loose %s inputs are supported: %s"
             extension requested;
      let file = resolve requested in
      match read file with
      | None -> probability_error "cannot inspect %s" file
      | Some object_ ->
        if not object_.ordinary then probability_error
          "%s is not an ordinary compilation unit" object_.unit_name;
        if Hashtbl.mem selected object_.unit_name
        then probability_error "duplicate unit %s" object_.unit_name;
        Hashtbl.add selected object_.unit_name (file, object_)) objfiles;
    let stdexit = resolve ("std_exit" ^ extension) in
    require_installation stdexit;
    if native then
      require_installation (Filename.remove_extension stdexit ^ Config.ext_obj);
    let checked = Hashtbl.create 64 in
    let roots = ref 0 in
    let origin record =
      List.filter (fun item -> item.vox_kind = Vox_probability_origin)
        record.vox_items
    in
    let check_record ~interface name record =
      let record = match record with
        | Some record -> record
        | None -> probability_error "%s has no verification record" name
      in
      if record.vox_status = Vox_not_verified
         || (not interface && record.vox_status <> Vox_verified)
      then probability_error "%s was not verified" name;
      if record.vox_solver <> ""
      then probability_error "%s used an unapproved solver" name;
      (match origin record with
      | [item] when String.starts_with
                      ~prefix:(Vox_trust.probability_profile ^ ":")
                      item.vox_name -> ()
      | _ -> probability_error "%s has no current admission record" name);
      if List.exists (fun flag ->
           List.mem flag (String.split_on_char ' ' record.vox_config))
           ["noassert=true"; "unsafe=true"]
      then probability_error "%s used unsafe compilation options" name;
      let kernel = match List.assoc_opt name probability_kernel with
        | None -> false
        | Some (implementation_hash, interface_hash) ->
          if List.exists (fun flag ->
               String.starts_with ~prefix:"open=" flag
               || String.starts_with ~prefix:"open_cmi=" flag
               || List.mem flag ["nopervasives=true"; "rectypes=true"])
               (String.split_on_char ' ' record.vox_config)
          then probability_error
            "%s used unsupported kernel compilation options" name;
          let expected = if interface then
              match interface_hash with
              | Some hash ->
                if record.vox_status <> Vox_interface then probability_error
                  "%s requires its reviewed explicit interface" name;
                hash
              | None ->
                if record.vox_status <> Vox_verified then probability_error
                  "%s requires an inferred interface" name;
                implementation_hash
            else implementation_hash in
          (match origin record with
          | [item] when item.vox_name =
              Vox_trust.probability_profile ^ ":" ^ expected ^ ":plain" -> true
          | _ -> probability_error "%s is not the reviewed kernel source" name)
      in
      if not kernel then List.iter (fun item ->
        match item.vox_kind with
        | Vox_probability_origin | Vox_probability_native_object -> ()
        | Vox_probability_root ->
          if not interface then begin
            if not (Hashtbl.mem selected name)
            then probability_error "%s has an unlinked credit root" name;
            roots := !roots + item.vox_count
          end
        | Vox_probability_forbidden | Vox_probability_external
        | Vox_refined_external | Vox_total_external | Vox_total_cast
        | Vox_builtin | Vox_cast_use | Vox_external | Vox_unsafe ->
          probability_error "%s uses %s (%s)" name item.vox_name
            item.vox_location) record.vox_items;
      record
    in
    let rec visit name expected =
      let cmi = match find name ".cmi" with
        | Some file -> file
        | None -> probability_error "%s has no interface" name in
      if List.mem name runtime_units && not (same_installation_file cmi)
      then probability_error "%s differs from the installed runtime" name;
      let interface, imports = match read_cmi cmi with
        | Some result -> result
        | None -> probability_error "cannot inspect %s" cmi in
      let actual = Option.join (List.assoc_opt name imports) in
      (match expected with
      | Some expected when actual <> Some expected ->
        probability_error "%s has a mismatched interface digest" name
      | _ -> ());
      if not (Hashtbl.mem checked name) then begin
        Hashtbl.add checked name ();
        if installed_interface name cmi then begin
          match Hashtbl.find_opt selected name with
          | None -> ()
          | Some (file, _) ->
            require_installation file;
            if native then require_installation
              (Filename.remove_extension file ^ Config.ext_obj)
        end else begin
          if List.mem name ["Borrow"; "Borrow_iarray"; "Vox_string_view"]
          then probability_error "%s uses prophecy" name;
          let file, object_ = match Hashtbl.find_opt selected name with
            | Some pair -> pair
            | None ->
              let file = match find name extension with
                | Some file -> file
                | None -> probability_error
                    "%s has no implementation for its proof dependencies" name
              in
              match read file with
              | Some object_ when object_.unit_name = name -> file, object_
              | _ -> probability_error "cannot inspect %s" file
          in
          if not object_.ordinary then probability_error
            "%s is not an ordinary compilation unit" name;
          (match Option.join (List.assoc_opt name object_.imports) with
          | Some _ -> ()
          | None -> probability_error "%s has no own-interface digest" name);
          let implementation = check_record ~interface:false name
            object_.record in
          if native then begin
            let hashes = List.filter (fun item ->
              item.vox_kind = Vox_probability_native_object)
              implementation.vox_items in
            match hashes with
            | [item] when item.vox_name = digest
                (Filename.remove_extension file ^ Config.ext_obj) -> ()
            | _ -> probability_error "%s has no matching native object" name
          end;
          let interface = check_record ~interface:true name interface in
          let all_imports = imports @ object_.imports @
            List.map recorded_import
              (implementation.vox_imports @ interface.vox_imports) in
          List.iter (fun (dependency, expected) ->
            (* Alias-only imports have no digest and add no assumptions. *)
            if Option.is_some expected then visit dependency expected)
            all_imports;
          List.iter (fun (dependency, expected) ->
            match expected with
            | None -> ()
            | Some expected ->
              let file, dependency_object =
                match Hashtbl.find_opt selected dependency with
                | Some pair -> pair
                | None ->
                  let file = resolve
                    (String.uncapitalize_ascii dependency ^ extension) in
                  match read file with
                  | Some object_ -> file, object_
                  | None -> probability_error "cannot inspect %s" file
              in
              if dependency_object.native_digest <> Some expected
              then probability_error "%s has a mismatched native digest"
                     dependency;
              (match find dependency ".cmi" with
              | Some cmi when installed_interface dependency cmi ->
                require_installation file
              | _ -> ());
              visit dependency None) object_.native_imports
        end
      end
    in
    Hashtbl.iter (fun name (_, object_) ->
      visit name (Option.join (List.assoc_opt name object_.imports))) selected;
    if !roots <> 1 then
      probability_error "expected one initial credit root, found %d" !roots
  end

let print_probability_admission () =
  if !Vox_trust.probabilistic then
    Format.printf "Vox probabilistic admission passed.@.\
      Assumptions: ideal fresh uniform draws and atomic sampling.@."
