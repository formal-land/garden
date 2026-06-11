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

let json_index value = json_z (Obj.magic value : M.z)

let json_option_pstring = function
  | None -> "null"
  | Some value -> json_pstring value

let json_list ?(indent = 0) json_item items =
  let pad = String.make indent ' ' in
  let item_pad = String.make (indent + 2) ' ' in
  match items with
  | [] -> "[]"
  | _ ->
      let buffer = Buffer.create 256 in
      Buffer.add_string buffer "[\n";
      let count = List.length items in
      List.iteri
        (fun index item ->
          let comma = if index + 1 = count then "" else "," in
          Buffer.add_string buffer item_pad;
          Buffer.add_string buffer (json_item item);
          Buffer.add_string buffer comma;
          Buffer.add_char buffer '\n')
        items;
      Buffer.add_string buffer pad;
      Buffer.add_char buffer ']';
      Buffer.contents buffer

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

let json_rotation (rotation : M.Rotation.t) = json_z rotation

let rec json_expression = function
  | M.Expression.Constant value ->
      Printf.sprintf "{\"tag\":\"Constant\",\"value\":%s}" (json_z value)
  | M.Expression.Selector selector ->
      Printf.sprintf "{\"tag\":\"Selector\",\"selector\":%s}" (json_index selector)
  | M.Expression.Fixed (column, rotation) ->
      Printf.sprintf "{\"tag\":\"Fixed\",\"column\":%s,\"rotation\":%s}"
        (json_index column)
        (json_rotation rotation)
  | M.Expression.Advice (column, rotation) ->
      Printf.sprintf "{\"tag\":\"Advice\",\"column\":%s,\"rotation\":%s}"
        (json_index column)
        (json_rotation rotation)
  | M.Expression.Instance_ (column, rotation) ->
      Printf.sprintf "{\"tag\":\"Instance_\",\"column\":%s,\"rotation\":%s}"
        (json_index column)
        (json_rotation rotation)
  | M.Expression.Negated expr ->
      Printf.sprintf "{\"tag\":\"Negated\",\"expr\":%s}" (json_expression expr)
  | M.Expression.Sum (left, right) ->
      Printf.sprintf "{\"tag\":\"Sum\",\"left\":%s,\"right\":%s}"
        (json_expression left)
        (json_expression right)
  | M.Expression.Product (left, right) ->
      Printf.sprintf "{\"tag\":\"Product\",\"left\":%s,\"right\":%s}"
        (json_expression left)
        (json_expression right)
  | M.Expression.Scaled (expr, scale) ->
      Printf.sprintf "{\"tag\":\"Scaled\",\"expr\":%s,\"scale\":%s}"
        (json_expression expr)
        (json_z scale)

let rec json_constraint = function
  | M.Constraint.Select (selector, constraint_) ->
      Printf.sprintf "{\"tag\":\"Select\",\"selector\":%s,\"constraint\":%s}"
        (json_index selector)
        (json_constraint constraint_)
  | M.Constraint.Equal (left, right) ->
      Printf.sprintf "{\"tag\":\"Equal\",\"left\":%s,\"right\":%s}"
        (json_expression left)
        (json_expression right)
  | M.Constraint.EqualZeroToPrecise expression ->
      json_expression expression

let json_named_constraint (name, constraint_) =
  Printf.sprintf "{\"name\":%s,\"constraint\":%s}"
    (json_option_pstring name)
    (json_constraint constraint_)

let json_gate (gate : M.Gate.t) =
  Printf.sprintf "{\"name\":%s,\"constraints\":%s}"
    (json_pstring gate.name)
    (json_list ~indent:0 json_named_constraint gate.constraints)

let json_lookup_pair (expression, fixed_column) =
  Printf.sprintf "{\"input\":%s,\"table\":%s}"
    (json_expression expression)
    (json_index fixed_column)

let json_lookup (lookup : M.LookupArgument.t) =
  Printf.sprintf "{\"pairs\":%s}"
    (json_list ~indent:0 json_lookup_pair lookup)

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

let write_synthesis_json path =
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      Printf.fprintf channel "{\n";
      Printf.fprintf channel "  \"events\": [\n";
      let event_count = List.length M.model_synthesis_events in
      List.iteri
        (fun index event ->
          let comma = if index + 1 = event_count then "" else "," in
          Printf.fprintf channel "    %s%s\n" (json_event event) comma)
        M.model_synthesis_events;
      Printf.fprintf channel "  ]\n";
      Printf.fprintf channel "}\n")

let write_configure_json path =
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      Printf.fprintf channel "{\n";
      Printf.fprintf channel "  \"configure\": {\n";
      Printf.fprintf channel "    \"gates\": %s,\n"
        (json_list ~indent:4 json_gate M.model_configure.gates);
      Printf.fprintf channel "    \"lookups\": %s\n"
        (json_list ~indent:4 json_lookup M.model_configure.lookups);
      Printf.fprintf channel "  }\n";
      Printf.fprintf channel "}\n")

let () =
  match Array.to_list Sys.argv with
  | [_; configure_output; synthesis_output] ->
      write_configure_json configure_output;
      write_synthesis_json synthesis_output
  | _ ->
      prerr_endline "usage: orchard_synthesis_json CONFIGURE.json SYNTHESIS.json";
      exit 2
