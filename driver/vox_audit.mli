(** Reading the Vox records of compiled units, and [-vox-audit]. *)

(** The records that earlier compilations left in the .cmo and .cmi files of
    this unit (see [Vox_trust.counterparts]). *)
val counterparts : Unit_info.t -> unit -> Cmi_format.vox_unit list

(** Print what the verification of the unit just compiled trusts, and what
    the units it depends on trust, found through the load path. *)
val print_unit :
  source_file:string -> current:string -> record:Cmi_format.vox_unit option
  -> unit

(** Native artifact inspection is supplied by the native driver, keeping
    the frontend independent of the native file format. *)
type probability_object =
  { unit_name : string;
    ordinary : bool;
    record : Cmi_format.vox_unit option;
    imports : (string * string option) list;
    native_imports : (string * string option) list;
    native_digest : string option }

val native_probability_object :
  (string -> probability_object option) ref

val check_probability_options : unit -> unit
val admit_probability : native:bool -> string list -> unit
val print_probability_admission : unit -> unit
