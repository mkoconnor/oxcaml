open Vox_smt

let config = { Vox_smt_solver.default_config with executable = Sys.argv.(1) }

let n = Symbol.create ~label:"n" Int63

let next = App (Sub, [Var n; Integer 1L])

let countdown facts =
  { datatypes = []; symbols = [n]; functions = [];
    facts;
    goal = { label = "decreases"; term = App (Lt, [next; Var n]) }
  }

let check query = (Vox_smt_solver.check ~config ~int_width:63 query).validity

let () =
  let positive = { label = "positive"; term = App (Gt, [Var n; Integer 0L]) } in
  (match check (countdown [positive]) with
   | Valid -> print_endline "n > 0 implies n - 1 < n: proved"
   | Failure message -> failwith message
   | _ -> failwith "guarded decrement was not proved");
  match check (countdown []) with
  | Invalid (Some [(symbol, Int_value value)])
    when symbol = n && value = -4611686018427387904L ->
      Printf.printf "n - 1 < n: refuted at n = %Ld (min_int)\n" value
  | Failure message -> failwith message
  | _ -> failwith "missing signed underflow counterexample"

let app op args = App (op, args)

let eq a b = app Eq [a; b]

let real_query ?(symbols = []) ?(facts = []) term =
  check
    {datatypes = []; symbols; functions = [];
     facts = List.map (fun term -> {label = "fact"; term}) facts;
     goal = {label = "real arithmetic"; term}}

let valid ?symbols ?facts term =
  match real_query ?symbols ?facts term with
  | Valid -> ()
  | Failure message -> failwith message
  | _ -> failwith "Exact real arithmetic was not proved"

let invalid ?symbols ?facts term =
  match real_query ?symbols ?facts term with
  | Invalid model -> model
  | Failure message -> failwith message
  | _ -> failwith "Expected a real counterexample"

let () =
  let real n = app Real_of_int [Big_integer n] in
  let fraction n d = app Real_div [real n; real d] in
  let half = fraction "1" "2" in
  let third = fraction "1" "3" in
  let r = Symbol.create ~label:"real" Real in
  let n = Symbol.create ~label:"integer" Int in
  valid (eq (app Real_add [half; third]) (fraction "5" "6"));
  valid (eq (app Real_sub [half; third]) (fraction "1" "6"));
  valid (eq (app Real_neg [half]) (fraction "-1" "2"));
  valid (eq (app Real_mul [half; third]) (fraction "1" "6"));
  valid (app Real_lt [third; half]);
  valid (app Real_le [third; half]);
  valid (app Real_gt [half; third]);
  valid (app Real_ge [half; third]);
  valid ~symbols:[r]
    (eq (app Real_sub [app Real_add [Var r; third]; third]) (Var r));
  valid ~symbols:[r] ~facts:[app Ne [Var r; real "0"]]
    (eq (app Real_div [Var r; Var r]) (real "1"));
  ignore (invalid ~symbols:[r]
    (eq (app Real_div [Var r; Var r]) (real "1")));
  valid ~symbols:[n]
    (eq (app Real_add [app Real_of_int [Var n]; real "1"])
      (app Real_of_int [app Int_add [Var n; Big_integer "1"]]));
  assert (invalid ~symbols:[r] ~facts:[eq (Var r) third]
    (app Real_gt [Var r; half]) = Some [r, Rational_value ("1", "3")]);
  assert (invalid ~symbols:[r] ~facts:[eq (Var r) (fraction "-7" "3")]
    (app Real_gt [Var r; real "0"])
    = Some [r, Rational_value ("-7", "3")]);
  assert (invalid ~symbols:[r]
    ~facts:[eq (app Real_mul [Var r; Var r]) (real "2")]
    (Boolean false) = None);
  valid (eq (app Real_sub
    [real "123456789012345678901234567891";
     real "123456789012345678901234567890"]) (real "1"));
  print_endline "Exact real arithmetic tests passed"
