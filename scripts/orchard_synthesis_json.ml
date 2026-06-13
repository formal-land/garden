module M = Orchard_synthesis_model

let rec integer_of_positive = function
  | M.XH -> Z.one
  | M.XO p -> Z.mul (integer_of_positive p) (Z.of_int 2)
  | M.XI p -> Z.succ (Z.mul (integer_of_positive p) (Z.of_int 2))

let string_of_z = function
  | M.Z0 -> "0"
  | M.Zpos p -> Z.to_string (integer_of_positive p)
  | M.Zneg p -> "-" ^ Z.to_string (integer_of_positive p)

let rec positive_of_int value =
  if value = 1 then M.XH
  else if value land 1 = 0 then M.XO (positive_of_int (value lsr 1))
  else M.XI (positive_of_int (value lsr 1))

let z_of_int value =
  if value = 0 then M.Z0
  else if value > 0 then M.Zpos (positive_of_int value)
  else M.Zneg (positive_of_int (-value))

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

let json_constant value =
  Printf.sprintf "{\"tag\":\"Constant\",\"value\":%s}" (json_z value)

let json_selector selector =
  Printf.sprintf "{\"tag\":\"Selector\",\"selector\":%s}" (json_index selector)

let json_negated expr =
  Printf.sprintf "{\"tag\":\"Negated\",\"expr\":%s}" expr

let json_inline_list json_item items =
  "[" ^ String.concat "," (List.map json_item items) ^ "]"

type json_expression_tree =
  | JsonAtom of string
  | JsonSum of json_expression_tree list
  | JsonProduct of json_expression_tree list

let rec json_expression_tree_to_string = function
  | JsonAtom json -> json
  | JsonSum args ->
      Printf.sprintf "{\"tag\":\"Sum\",\"args\":%s}"
        (json_inline_list json_expression_tree_to_string args)
  | JsonProduct args ->
      Printf.sprintf "{\"tag\":\"Product\",\"args\":%s}"
        (json_inline_list json_expression_tree_to_string args)

let json_negated_tree expr =
  JsonAtom (json_negated (json_expression_tree_to_string expr))

let json_sum_tree left right =
  let left_args =
    match left with
    | JsonSum args -> args
    | _ -> [left]
  in
  let right_args =
    match right with
    | JsonSum args -> args
    | _ -> [right]
  in
  JsonSum (left_args @ right_args)

let json_product_tree left right =
  let left_args =
    match left with
    | JsonProduct args -> args
    | _ -> [left]
  in
  let right_args =
    match right with
    | JsonProduct args -> args
    | _ -> [right]
  in
  JsonProduct (left_args @ right_args)

let rec json_expression_tree = function
  | M.Expression.Constant value ->
      JsonAtom (json_constant value)
  | M.Expression.Selector selector ->
      JsonAtom (json_selector selector)
  | M.Expression.Fixed (column, rotation) ->
      JsonAtom (
        Printf.sprintf "{\"tag\":\"Fixed\",\"column\":%s,\"rotation\":%s}"
          (json_index column)
          (json_rotation rotation))
  | M.Expression.Advice (column, rotation) ->
      JsonAtom (
        Printf.sprintf "{\"tag\":\"Advice\",\"column\":%s,\"rotation\":%s}"
          (json_index column)
          (json_rotation rotation))
  | M.Expression.Instance_ (column, rotation) ->
      JsonAtom (
        Printf.sprintf "{\"tag\":\"Instance_\",\"column\":%s,\"rotation\":%s}"
          (json_index column)
          (json_rotation rotation))
  | M.Expression.Negated expr ->
      json_negated_tree (json_expression_tree expr)
  | M.Expression.Sum (left, right) ->
      json_sum_tree (json_expression_tree left) (json_expression_tree right)
  | M.Expression.Product (left, right) ->
      json_product_tree (json_expression_tree left) (json_expression_tree right)
  | M.Expression.Scaled (expr, scale) ->
      JsonAtom (
        Printf.sprintf "{\"tag\":\"Scaled\",\"expr\":%s,\"scale\":%s}"
          (json_expression_tree_to_string (json_expression_tree expr))
          (json_z scale))

let json_expression expression =
  json_expression_tree_to_string (json_expression_tree expression)

let rec int_of_nat = function
  | M.O -> 0
  | M.S n -> 1 + int_of_nat n

let json_difference_tree left right = json_sum_tree left (json_negated_tree right)

let json_range_check expression range =
  let word = json_expression_tree expression in
  let range = int_of_nat range in
  let rec go acc i =
    if i >= range then acc
    else
      go
        (json_product_tree
          acc
          (json_difference_tree (JsonAtom (json_constant (z_of_int i))) word))
        (i + 1)
  in
  go word 1

let rec json_constraint_tree = function
  | M.Constraint.Select (selector, constraint_) ->
      json_product_tree
        (JsonAtom (json_selector selector))
        (json_constraint_tree constraint_)
  | M.Constraint.Equal (left, right) ->
      json_difference_tree (json_expression_tree left) (json_expression_tree right)
  | M.Constraint.Boolean expression ->
      json_range_check expression (M.S (M.S M.O))
  | M.Constraint.Range (expression, range) ->
      json_range_check expression range
  | M.Constraint.Either (left, right) ->
      json_product_tree (json_constraint_tree left) (json_constraint_tree right)
  | M.Constraint.EqualZeroToPrecise expression ->
      json_expression_tree expression

let json_constraint constraint_ =
  json_expression_tree_to_string (json_constraint_tree constraint_)

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
