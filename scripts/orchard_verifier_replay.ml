module M = Orchard_verifier_replay

let elapsed start = Unix.gettimeofday () -. start

let rec failed_indices index = function
  | [] -> []
  | true :: rest -> failed_indices (index + 1) rest
  | false :: rest -> index :: failed_indices (index + 1) rest

let render_indices indices =
  String.concat "," (List.map string_of_int indices)

let run_case_zero () =
  let start = Unix.gettimeofday () in
  let matched =
    M.OrchardVerifierSnapshotExtract.run_case Big_int_Z.zero_big_int
  in
  Printf.printf "case=0 matched=%b elapsed_seconds=%.6f\n%!"
    matched (elapsed start);
  if not matched then exit 1

let run_all () =
  let start = Unix.gettimeofday () in
  let vector, summary = M.OrchardVerifierSnapshotExtract.run_all () in
  let seconds = elapsed start in
  let failures = failed_indices 0 vector in
  let count = List.length vector in
  Printf.printf
    "cases=%d matched=%d summary=%b failures=[%s] elapsed_seconds=%.6f\n%!"
    count (count - List.length failures) summary (render_indices failures)
    seconds;
  if count <> 40 || failures <> [] || not summary then exit 1

let () =
  match Array.to_list Sys.argv with
  | [_; "--case0"] -> run_case_zero ()
  | [_; "--all"] -> run_all ()
  | _ ->
      prerr_endline "usage: orchard_verifier_replay (--case0 | --all)";
      exit 2
