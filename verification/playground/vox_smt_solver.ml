(* The browser implementation of [Vox_smt_solver]: the same interface as the
   native one in ../vox_smt_solver.ml, but the solver is Z3 compiled to
   WebAssembly and loaded in the same worker. The page installs
   [globalThis.voxZ3Eval], which runs SMT-LIB text with [Z3_eval_smtlib2_string]
   (in a fresh Z3 context for each query) and returns what Z3 printed. The call
   is synchronous, so the verifier runs unchanged. *)

open Vox_smt

type config =
  { executable : string;
    timeout_ms : int
  }

let default_config = { executable = "z3"; timeout_ms = 5000 }

let expected_version = Vox_smt_response.expected_version

let is_expected_version = Vox_smt_response.is_expected_version

(* The page installs [globalThis.voxZ3Version], what the loaded Z3 answers to
   [(get-info :version)]. It is reported as [z3 -version] reports it, with the
   word size replaced by "WebAssembly", so that the version is checked as
   natively and the solver's identity differs from that of a native Z3. *)
let version ~executable:_ =
  let open Js_of_ocaml in
  let version = Js.Unsafe.pure_js_expr "globalThis.voxZ3Version" in
  if Js.Optdef.test version
  then
    match String.trim (Js.to_string version) with
    | "" -> None
    | version -> Some ("Z3 version " ^ version ^ " - WebAssembly")
  else None

let monotonic_time () =
  Js_of_ocaml.Js.Unsafe.meth_call
    (Js_of_ocaml.Js.Unsafe.pure_js_expr "globalThis.performance")
    "now" [||]
  /. 1000.

type result =
  { validity : validity;
    stderr : string;
    resources : int option;
    core : Symbol.t list option;
    encoding_seconds : float;
    solving_seconds : float
  }

exception Cancelled

exception Solver_error of string

(* Z3 reports errors in its output as [(error "...")] and keeps going, like the
   native process. The JavaScript side raises only when Z3 itself fails (for
   example, when it runs out of memory). *)
let eval text =
  let open Js_of_ocaml in
  let eval = Js.Unsafe.pure_js_expr "globalThis.voxZ3Eval" in
  if Js.Optdef.test eval |> not then raise (Solver_error "Z3 is not loaded");
  match Js.Unsafe.fun_call eval [| Js.Unsafe.inject (Js.string text) |] with
  | output -> Js.to_string output
  | exception Js_error.Exn error ->
    raise (Solver_error (Js_error.message error))

let first_line text =
  let rec skip text =
    match String.index_opt text '\n' with
    | None -> String.trim text, ""
    | Some i ->
      let line = String.trim (String.sub text 0 i) in
      let rest = String.sub text (i + 1) (String.length text - i - 1) in
      if line = "" then skip rest else line, rest
  in
  skip text

let report_query (query : query) script validity =
  let open Js_of_ocaml in
  let report = Js.Unsafe.pure_js_expr "globalThis.voxProofQuery" in
  if Js.Optdef.test report
  then begin
    let names label prefix items =
      List.mapi
        (fun i item ->
          let name = label item in
          let duplicate =
            List.exists (fun other -> other <> item && label other = name) items
          in
          ( item,
            if duplicate
            then name ^ "[" ^ prefix ^ string_of_int i ^ "]"
            else name ))
        items
    in
    let symbols = names Symbol.label "v" query.symbols in
    let functions = names Function.label "f" query.functions in
    let operator = function
      | Add | Int_add | Real_add -> "+"
      | Sub | Int_sub | Real_sub -> "-"
      | Mul | Int_mul | Real_mul -> "*"
      | Div | Int_div | Real_div -> "/"
      | Rem | Int_mod -> "mod"
      | Neg | Int_neg | Real_neg -> "negate"
      | Eq -> "="
      | Ne -> "<>"
      | Lt | Int_lt | Real_lt -> "<"
      | Le | Int_le | Real_le -> "<="
      | Gt | Int_gt | Real_gt -> ">"
      | Ge | Int_ge | Real_ge -> ">="
      | Not -> "not"
      | And -> "&&"
      | Or -> "||"
      | Implies -> "implies"
      | Ite -> "if"
      | Bit_and -> "land"
      | Bit_or -> "lor"
      | Bit_xor -> "lxor"
      | Shift_left -> "lsl"
      | Shift_right_logical -> "lsr"
      | Shift_right_arithmetic -> "asr"
      | Int_of_int63 -> "Bigint.of_int"
      | Int63_of_int -> "int_of_bigint"
      | Real_of_int -> "Real.of_bigint"
    in
    let rec term depth = function
      | _ when depth = 0 -> "…"
      | Boolean b -> string_of_bool b
      | Integer n -> Int64.to_string n
      | Big_integer n -> n ^ "Z"
      | Var s -> List.assoc s symbols
      | Call (f, args) -> application depth (List.assoc f functions) args
      | Construct (c, args) -> application depth (Constructor.label c) args
      | Is (c, t) -> application depth ("is " ^ Constructor.label c) [t]
      | Select (c, i, t) ->
        application depth (Constructor.label c ^ "." ^ string_of_int i) [t]
      | App (op, [a; b]) ->
        "("
        ^ term (depth - 1) a
        ^ " " ^ operator op ^ " "
        ^ term (depth - 1) b
        ^ ")"
      | App (op, args) -> application depth (operator op) args
    and application depth name args =
      name ^ "(" ^ String.concat ", " (List.map (term (depth - 1)) args) ^ ")"
    in
    let text s = Js.Unsafe.inject (Js.string s) in
    let array xs = Js.Unsafe.inject (Js.array (Array.of_list xs)) in
    let status, reason, model =
      match validity with
      | Valid -> "valid", "", Some []
      | Invalid model -> "invalid", "", model
      | Unknown reason -> "unknown", Option.value reason ~default:"", Some []
      | Timeout -> "timeout", "", Some []
      | Failure reason -> "failure", reason, Some []
    in
    let value (symbol, value) =
      let contents =
        match value with
        | Bool_value b -> string_of_bool b
        | Int_value n -> Int64.to_string n
        | Bigint_value n -> n ^ "Z"
        | Rational_value (n, d) -> n ^ "/" ^ d
      in
      Js.Unsafe.obj
        [| "name", text (List.assoc symbol symbols); "value", text contents |]
    in
    let description =
      Js.Unsafe.obj
        [| "label", text query.goal.label;
           "goal", text (term 8 query.goal.term);
           ( "assumptions",
             array
               (List.map
                  (fun fact ->
                    Js.Unsafe.obj
                      [| "label", text fact.label;
                         "text", text (term 8 fact.term)
                      |])
                  query.facts) );
           "status", text status;
           "reason", text reason;
           "values", array (List.map value (Option.value model ~default:[]));
           "modelAvailable", Js.Unsafe.inject (Js.bool (Option.is_some model));
           ( "functions",
             array (List.map (fun (_, name) -> Js.string name) functions) );
           "script", text script
        |]
    in
    ignore (Js.Unsafe.fun_call report [| Js.Unsafe.inject description |])
  end

let check_impl ?(config = default_config) ?(dump = fun _ -> ())
    ?(cancelled = fun () -> false) ?(request_model = true) ?resource_limit
    ?assumptions ~int_width q =
  if config.timeout_ms <= 0 then invalid_arg "Vox_smt_solver: timeout_ms";
  let started = monotonic_time () in
  if cancelled () then raise Cancelled;
  let input =
    to_smtlib
      ~poll:(fun () -> if cancelled () then raise Cancelled)
      ?resource_limit ?assumptions ~int_width ~timeout_ms:config.timeout_ms q
  in
  let encoded = monotonic_time () in
  let resources = ref None and core = ref None in
  let validity =
    try
      let input = Vox_smt_response.session_input input in
      dump input;
      let answer, rest = first_line (eval input) in
      let request =
        Vox_smt_response.followup ~request_model ?assumptions q.symbols answer
        ^ Vox_smt_response.resource_request
      in
      dump request;
      let response = rest ^ eval request in
      (* Z3's own [:timeout] option, set by [to_smtlib], stands in for the
         native runner's deadline: it answers unknown with reason timeout. *)
      Vox_smt_response.interpret_response ~request_model ~resources ?assumptions
        ~core q.symbols answer response
    with
    | Vox_smt_response.Protocol_error message -> Failure message
    | Solver_error message -> Failure message
  in
  let finished = monotonic_time () in
  report_query q input validity;
  { validity;
    stderr = "";
    resources = !resources;
    core = (match validity with Valid -> !core | _ -> None);
    encoding_seconds = encoded -. started;
    solving_seconds = finished -. encoded
  }

let with_session ?config ?dump ?cancelled ~int_width f =
  let closed = ref false and busy = ref false in
  Fun.protect
    ~finally:(fun () -> closed := true)
    (fun () ->
      f (fun ?request_model ?resource_limit ?assumptions query ->
          if !closed then invalid_arg "Vox_smt_solver: closed session";
          if !busy then invalid_arg "Vox_smt_solver: recursive session query";
          busy := true;
          Fun.protect
            ~finally:(fun () -> busy := false)
            (fun () ->
              check_impl ?request_model ?config ?dump ?cancelled ?resource_limit
                ?assumptions ~int_width query)))

let with_incremental_session ?config ?dump ?cancelled ~int_width f =
  with_session ?config ?dump ?cancelled ~int_width f

let with_automatic_session ?config ?dump ?cancelled ~int_width f =
  with_session ?config ?dump ?cancelled ~int_width f

let check ?request_model ?config ?dump ?cancelled ?resource_limit ?assumptions
    ~int_width query =
  with_session ?config ?dump ?cancelled ~int_width (fun check ->
      check ?request_model ?resource_limit ?assumptions query)
