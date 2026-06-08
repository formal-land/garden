module M = Orchard_synthesis_model

let rec integer_of_positive = function
  | M.XH -> Z.one
  | M.XO p -> Z.mul (integer_of_positive p) (Z.of_int 2)
  | M.XI p -> Z.succ (Z.mul (integer_of_positive p) (Z.of_int 2))

let string_of_z = function
  | M.Z0 -> "0"
  | M.Zpos p -> Z.to_string (integer_of_positive p)
  | M.Zneg p -> "-" ^ Z.to_string (integer_of_positive p)

let json_string value =
  let buffer = Buffer.create (String.length value + 2) in
  let add_hex byte =
    let hex = "0123456789abcdef" in
    Buffer.add_string buffer "\\u00";
    Buffer.add_char buffer hex.[byte lsr 4];
    Buffer.add_char buffer hex.[byte land 0xf]
  in
  Buffer.add_char buffer '"';
  String.iter
    (fun char ->
      match char with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\b' -> Buffer.add_string buffer "\\b"
      | '\012' -> Buffer.add_string buffer "\\f"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | char when Char.code char < 0x20 -> add_hex (Char.code char)
      | char -> Buffer.add_char buffer char)
    value;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let json_pstring value = json_string (Pstring.to_string value)

let json_z value = json_string (string_of_z value)

let string_of_column_kind = function
  | M.Raw.ColumnKind.Advice -> "Advice"
  | M.Raw.ColumnKind.Fixed -> "Fixed"
  | M.Raw.ColumnKind.Instance_ -> "Instance_"

let json_column_ref (column : M.Raw.ColumnRef.t) =
  Printf.sprintf "{\"kind\":%s,\"index\":%s}"
    (json_string (string_of_column_kind column.kind))
    (json_z column.index)

let json_cell (cell : M.Raw.Cell.t) =
  Printf.sprintf "{\"column\":%s,\"row\":%s}"
    (json_column_ref cell.column)
    (json_z cell.row)

let json_event = function
  | M.Raw.Event.EnterRegion name ->
      Printf.sprintf "{\"tag\":\"EnterRegion\",\"name\":%s}" (json_pstring name)
  | M.Raw.Event.ExitRegion name ->
      Printf.sprintf "{\"tag\":\"ExitRegion\",\"name\":%s}" (json_pstring name)
  | M.Raw.Event.PushNamespace name ->
      Printf.sprintf "{\"tag\":\"PushNamespace\",\"name\":%s}" (json_pstring name)
  | M.Raw.Event.PopNamespace name ->
      Printf.sprintf "{\"tag\":\"PopNamespace\",\"name\":%s}" (json_pstring name)
  | M.Raw.Event.EnableSelector (selector, row, annotation) ->
      Printf.sprintf
        "{\"tag\":\"EnableSelector\",\"selector\":%s,\"row\":%s,\"annotation\":%s}"
        (json_z selector)
        (json_z row)
        (json_pstring annotation)
  | M.Raw.Event.AssignFixed (column, row, annotation, value) ->
      Printf.sprintf
        "{\"tag\":\"AssignFixed\",\"column\":%s,\"row\":%s,\"annotation\":%s,\"value\":%s}"
        (json_z column)
        (json_z row)
        (json_pstring annotation)
        (json_z value)
  | M.Raw.Event.Copy (left, right) ->
      Printf.sprintf "{\"tag\":\"Copy\",\"left\":%s,\"right\":%s}"
        (json_cell left)
        (json_cell right)
  | M.Raw.Event.FillFromRow (column, from_row, value) ->
      Printf.sprintf
        "{\"tag\":\"FillFromRow\",\"column\":%s,\"from_row\":%s,\"value\":%s}"
        (json_z column)
        (json_z from_row)
        (json_z value)

let write_json path =
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      Printf.fprintf channel "{\n";
      Printf.fprintf channel "  \"schema\": %s,\n" (json_pstring M.schema);
      Printf.fprintf channel "  \"source\": %s,\n" (json_pstring M.source);
      Printf.fprintf channel
        "  \"event_default\": {\"tag\":\"EnterRegion\",\"name\":\"\"},\n";
      Printf.fprintf channel "  \"events\": [\n";
      let event_count = List.length M.model_events in
      List.iteri
        (fun index event ->
          let comma = if index + 1 = event_count then "" else "," in
          Printf.fprintf channel "    %s%s\n" (json_event event) comma)
        M.model_events;
      Printf.fprintf channel "  ]\n";
      Printf.fprintf channel "}\n")

let () =
  match Array.to_list Sys.argv with
  | [_; output] -> write_json output
  | _ ->
      prerr_endline "usage: orchard_synthesis_json OUT.json";
      exit 2
