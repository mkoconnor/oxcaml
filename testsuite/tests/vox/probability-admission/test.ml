(* TEST
 has-z3;
 source_directories =
   "${test_source_directory}/../../../../verification/library";
 prebuilt_modules = "vox_sequence.mli vox_sequence.ml";
 prebuilt_modules += " vox_real.mli vox_real.ml";
 prebuilt_modules += " vox_real_credits.mli vox_real_credits.ml";
 prebuilt_modules += " vox_expectation.ml";
 prebuilt_modules += " vox_probability.mli vox_probability.ml";
 prebuilt_modules += " borrow.mli borrow.ml";
 readonly_files = "run.sh";
 {
   arguments = "${test_source_directory}/run.sh";
   arguments += " ${ocamlc_opt} ${ocamlsrcdir}/stdlib cmo";
   bytecode;
 }
 {
   arguments = "${test_source_directory}/run.sh";
   arguments += " ${ocamlopt_byte} ${ocamlsrcdir}/stdlib cmx";
   setup-ocamlopt.byte-build-env;
   ocamlopt.byte;
   check-ocamlopt.byte-output;
   run;
   check-program-output;
 }
*)

let () =
  let arguments = List.tl (Array.to_list Sys.argv) in
  exit (Sys.command (Filename.quote_command "sh" arguments))
