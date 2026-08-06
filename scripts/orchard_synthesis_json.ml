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

let json_z_number value = string_of_z value

let json_bool value = if value then "true" else "false"

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
  | M.Constraint.EitherZeroToPrecise (left, right) ->
      json_product_tree (json_expression_tree left) (json_expression_tree right)
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

(* The structural trace keeps Garden's semantic constraint constructors,
   unlike the configure parity artifact above, which intentionally lowers
   every constraint to one polynomial expression. *)
let rec json_semantic_constraint = function
  | M.Constraint.Select (selector, constraint_) ->
      Printf.sprintf
        "{\"tag\":\"Select\",\"selector\":%s,\"constraint\":%s}"
        (json_index selector)
        (json_semantic_constraint constraint_)
  | M.Constraint.Equal (left, right) ->
      Printf.sprintf "{\"tag\":\"Equal\",\"left\":%s,\"right\":%s}"
        (json_expression left)
        (json_expression right)
  | M.Constraint.Boolean expression ->
      Printf.sprintf "{\"tag\":\"Boolean\",\"expression\":%s}"
        (json_expression expression)
  | M.Constraint.Range (expression, range) ->
      Printf.sprintf
        "{\"tag\":\"Range\",\"expression\":%s,\"range\":%d}"
        (json_expression expression)
        (int_of_nat range)
  | M.Constraint.Either (left, right) ->
      Printf.sprintf "{\"tag\":\"Either\",\"left\":%s,\"right\":%s}"
        (json_semantic_constraint left)
        (json_semantic_constraint right)
  | M.Constraint.EitherZeroToPrecise (left, right) ->
      Printf.sprintf
        "{\"tag\":\"EitherZeroToPrecise\",\"left\":%s,\"right\":%s}"
        (json_expression left)
        (json_expression right)
  | M.Constraint.EqualZeroToPrecise expression ->
      Printf.sprintf
        "{\"tag\":\"EqualZeroToPrecise\",\"expression\":%s}"
        (json_expression expression)

let json_trace_named_constraint (name, constraint_) =
  Printf.sprintf "{\"name\":%s,\"constraint\":%s}"
    (json_option_pstring name)
    (json_semantic_constraint constraint_)

let json_trace_gate (gate : M.Gate.t) =
  Printf.sprintf
    "{\"name\":%s,\"constraint_count\":%d,\"constraints\":%s}"
    (json_pstring gate.name)
    (List.length gate.constraints)
    (json_list ~indent:0 json_trace_named_constraint gate.constraints)

let lowercase_column_kind = function
  | M.Raw.ColumnKind.Advice -> "advice"
  | M.Raw.ColumnKind.Fixed -> "fixed"
  | M.Raw.ColumnKind.Instance_ -> "instance"

let json_option_z = function
  | None -> "null"
  | Some value -> json_z value

let trace_cell_id (cell : M.HighLevelTrace.Cell.t) =
  let kind = lowercase_column_kind cell.column.kind in
  let column = string_of_z cell.column.index in
  match cell.column.kind, cell.region_index with
  | M.Raw.ColumnKind.Instance_, _ ->
      Printf.sprintf "cell:%s:%s:row:%s"
        kind column (string_of_z cell.offset)
  | _, Some region ->
      Printf.sprintf "cell:%s:%s:region:%s:offset:%s"
        kind column (string_of_z region) (string_of_z cell.offset)
  | _, None ->
      Printf.sprintf "cell:%s:%s:offset:%s"
        kind column (string_of_z cell.offset)

let json_trace_cell (cell : M.HighLevelTrace.Cell.t) =
  Printf.sprintf
    "{\"id\":%s,\"column\":%s,\"region_index\":%s,\"offset\":%s,\"absolute_row\":%s}"
    (json_string (trace_cell_id cell))
    (json_column_ref cell.column)
    (json_option_z cell.region_index)
    (json_z cell.offset)
    (json_z cell.absolute_row)

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
  | M.Raw.Event.FillFromRow (column, from_row, _to_row, value) ->
      Printf.sprintf
        "{\"tag\":\"FillFromRow\",\"column\":%s,\"from_row\":%s,\"value\":%s}"
        (json_z column)
        (json_z from_row)
        (json_z value)

type configure_trace_stats = {
  mutable configure_gate_count : int;
  mutable configure_lookup_count : int;
  mutable configure_constraint_count : int;
}

let json_configure_trace_operation stats operation_index = function
  | M.HighLevelTrace.ConfigureOp.CreateGate gate ->
      let gate_index = stats.configure_gate_count in
      stats.configure_gate_count <- gate_index + 1;
      stats.configure_constraint_count <-
        stats.configure_constraint_count + List.length gate.constraints;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"create_gate\",\"gate_id\":%s,\"gate_index\":%d,\"gate\":%s}"
        (json_string (Printf.sprintf "configure-op:%d" operation_index))
        (json_string (Printf.sprintf "gate:%d" gate_index))
        gate_index
        (json_trace_gate gate)
  | M.HighLevelTrace.ConfigureOp.CreateLookup lookup ->
      let lookup_index = stats.configure_lookup_count in
      stats.configure_lookup_count <- lookup_index + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"create_lookup\",\"lookup_id\":%s,\"lookup_index\":%d,\"lookup\":%s}"
        (json_string (Printf.sprintf "configure-op:%d" operation_index))
        (json_string (Printf.sprintf "lookup-argument:%d" lookup_index))
        lookup_index
        (json_lookup lookup)
  | M.HighLevelTrace.ConfigureOp.Metadata _ ->
      failwith "metadata operations are rendered in vk_metadata"

type layout_trace_stats = {
  mutable layout_node_count : int;
  mutable layout_namespace_count : int;
  mutable layout_region_count : int;
  mutable layout_constrain_instance_count : int;
  mutable layout_lookup_table_count : int;
  mutable layout_lookup_column_count : int;
  mutable layout_region_operation_count : int;
  mutable layout_selector_enable_count : int;
  mutable layout_fixed_assignment_count : int;
  mutable layout_copy_count : int;
  mutable layout_constant_count : int;
}

let json_region_operation stats region_index operation_index = function
  | M.HighLevelTrace.RegionOp.EnableSelector
      (selector, offset, absolute_row, annotation) ->
      stats.layout_region_operation_count <-
        stats.layout_region_operation_count + 1;
      stats.layout_selector_enable_count <-
        stats.layout_selector_enable_count + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"enable_selector\",\"selector_id\":%s,\"selector\":%s,\"offset\":%s,\"absolute_row\":%s,\"annotation\":%s}"
        (json_string
          (Printf.sprintf "region:%s/op:%d"
            (string_of_z region_index) operation_index))
        (json_string (Printf.sprintf "selector:%s" (string_of_z selector)))
        (json_z selector)
        (json_z offset)
        (json_z absolute_row)
        (json_pstring annotation)
  | M.HighLevelTrace.RegionOp.AssignFixed (cell, annotation, value) ->
      stats.layout_region_operation_count <-
        stats.layout_region_operation_count + 1;
      stats.layout_fixed_assignment_count <-
        stats.layout_fixed_assignment_count + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"assign_fixed\",\"cell\":%s,\"annotation\":%s,\"value\":%s}"
        (json_string
          (Printf.sprintf "region:%s/op:%d"
            (string_of_z region_index) operation_index))
        (json_trace_cell cell)
        (json_pstring annotation)
        (json_z value)
  | M.HighLevelTrace.RegionOp.Copy (lhs, rhs) ->
      stats.layout_region_operation_count <-
        stats.layout_region_operation_count + 1;
      stats.layout_copy_count <- stats.layout_copy_count + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"copy\",\"lhs\":%s,\"rhs\":%s}"
        (json_string
          (Printf.sprintf "region:%s/op:%d"
            (string_of_z region_index) operation_index))
        (json_trace_cell lhs)
        (json_trace_cell rhs)
  | M.HighLevelTrace.RegionOp.ConstrainConstant (cell, value) ->
      stats.layout_region_operation_count <-
        stats.layout_region_operation_count + 1;
      stats.layout_constant_count <- stats.layout_constant_count + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"constrain_constant\",\"cell\":%s,\"value\":%s}"
        (json_string
          (Printf.sprintf "region:%s/op:%d"
            (string_of_z region_index) operation_index))
        (json_trace_cell cell)
        (json_z value)

let json_lookup_table_entry (entry : M.HighLevelTrace.LookupTableEntry.t) =
  Printf.sprintf
    "{\"id\":%s,\"column\":%s,\"annotation\":%s,\"value_count\":%d,\"default_value\":%s}"
    (json_string (Printf.sprintf "lookup-column:%s" (string_of_z entry.column)))
    (json_z entry.column)
    (json_pstring entry.annotation)
    (int_of_nat entry.value_count)
    (json_z entry.default_value)

let rec json_layout_node stats = function
  | M.HighLevelTrace.LayoutNode.Namespace (name, children) ->
      let namespace_index = stats.layout_namespace_count in
      stats.layout_node_count <- stats.layout_node_count + 1;
      stats.layout_namespace_count <- namespace_index + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"namespace\",\"name\":%s,\"children\":%s}"
        (json_string (Printf.sprintf "namespace:%d" namespace_index))
        (json_pstring name)
        (json_list ~indent:0 (json_layout_node stats) children)
  | M.HighLevelTrace.LayoutNode.Region
      (region_index, start_row, name, operations) ->
      stats.layout_node_count <- stats.layout_node_count + 1;
      stats.layout_region_count <- stats.layout_region_count + 1;
      let operations =
        List.mapi (json_region_operation stats region_index) operations
      in
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"region\",\"region_index\":%s,\"start_row\":%s,\"name\":%s,\"operations\":%s}"
        (json_string (Printf.sprintf "region:%s" (string_of_z region_index)))
        (json_z region_index)
        (json_z start_row)
        (json_pstring name)
        (json_list ~indent:0 (fun operation -> operation) operations)
  | M.HighLevelTrace.LayoutNode.ConstrainInstance
      (source_cell, instance_column, row) ->
      let layout_operation_index = stats.layout_constrain_instance_count in
      stats.layout_node_count <- stats.layout_node_count + 1;
      stats.layout_constrain_instance_count <- layout_operation_index + 1;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"constrain_instance\",\"source\":%s,\"instance_cell_id\":%s,\"instance_column\":%s,\"row\":%s}"
        (json_string (Printf.sprintf "layout-op:%d" layout_operation_index))
        (json_trace_cell source_cell)
        (json_string
          (Printf.sprintf "cell:instance:%s:row:%s"
            (string_of_z instance_column) (string_of_z row)))
        (json_z instance_column)
        (json_z row)
  | M.HighLevelTrace.LayoutNode.InitLookupTables (name, entries) ->
      let lookup_table_index = stats.layout_lookup_table_count in
      stats.layout_node_count <- stats.layout_node_count + 1;
      stats.layout_lookup_table_count <- lookup_table_index + 1;
      stats.layout_lookup_column_count <-
        stats.layout_lookup_column_count + List.length entries;
      Printf.sprintf
        "{\"id\":%s,\"kind\":\"init_lookup_tables\",\"name\":%s,\"entries\":%s}"
        (json_string (Printf.sprintf "lookup-tables:%d" lookup_table_index))
        (json_pstring name)
        (json_list ~indent:0 json_lookup_table_entry entries)

let write_structure_json path =
  let configure_stats = {
    configure_gate_count = 0;
    configure_lookup_count = 0;
    configure_constraint_count = 0;
  } in
  let configure_operations =
    let visible_operations =
      List.filter
        (function
          | M.HighLevelTrace.ConfigureOp.Metadata _ -> false
          | _ -> true)
        M.model_configure_trace
    in
    List.mapi
      (json_configure_trace_operation configure_stats)
      visible_operations
  in
  let layout_stats = {
    layout_node_count = 0;
    layout_namespace_count = 0;
    layout_region_count = 0;
    layout_constrain_instance_count = 0;
    layout_lookup_table_count = 0;
    layout_lookup_column_count = 0;
    layout_region_operation_count = 0;
    layout_selector_enable_count = 0;
    layout_fixed_assignment_count = 0;
    layout_copy_count = 0;
    layout_constant_count = 0;
  } in
  let layout_nodes =
    List.map (json_layout_node layout_stats) M.model_layout_trace
  in
  let channel = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      Printf.fprintf channel "{\n";
      Printf.fprintf channel
        "  \"schema\": \"garden.orchard.circuit-structure.raw.v1\",\n";
      Printf.fprintf channel "  \"configure\": {\n";
      Printf.fprintf channel "    \"operations\": %s,\n"
        (json_list ~indent:4 (fun operation -> operation) configure_operations);
      Printf.fprintf channel
        "    \"summary\": {\"operation_count\":%d,\"gate_count\":%d,\"lookup_count\":%d,\"constraint_count\":%d}\n"
        (List.length configure_operations)
        configure_stats.configure_gate_count
        configure_stats.configure_lookup_count
        configure_stats.configure_constraint_count;
      Printf.fprintf channel "  },\n";
      Printf.fprintf channel "  \"synthesis\": {\n";
      Printf.fprintf channel "    \"nodes\": %s,\n"
        (json_list ~indent:4 (fun node -> node) layout_nodes);
      Printf.fprintf channel
        "    \"summary\": {\"root_node_count\":%d,\"node_count\":%d,\"namespace_count\":%d,\"region_count\":%d,\"constrain_instance_count\":%d,\"lookup_table_init_count\":%d,\"lookup_column_count\":%d,\"region_operation_count\":%d,\"selector_enable_count\":%d,\"fixed_assignment_count\":%d,\"copy_count\":%d,\"constant_count\":%d}\n"
        (List.length layout_nodes)
        layout_stats.layout_node_count
        layout_stats.layout_namespace_count
        layout_stats.layout_region_count
        layout_stats.layout_constrain_instance_count
        layout_stats.layout_lookup_table_count
        layout_stats.layout_lookup_column_count
        layout_stats.layout_region_operation_count
        layout_stats.layout_selector_enable_count
        layout_stats.layout_fixed_assignment_count
        layout_stats.layout_copy_count
        layout_stats.layout_constant_count;
      Printf.fprintf channel "  }\n";
      Printf.fprintf channel "}\n")

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
  let metadata = M.model_configure_metadata in
  let counts = metadata.counts in
  let queries = metadata.queries in
  let json_query (column, rotation) =
    Printf.sprintf "{\"column\":%s,\"rotation\":%s}"
      (json_z_number column)
      (json_z_number rotation)
  in
  let json_indexed_kind = function
    | M.Metadata.IndexedColumn.Advice -> json_string "advice"
    | M.Metadata.IndexedColumn.Fixed -> json_string "fixed"
    | M.Metadata.IndexedColumn.Instance_ -> json_string "instance"
  in
  let json_indexed_column (column : M.Metadata.IndexedColumn.t) =
    Printf.sprintf "{\"kind\":%s,\"index\":%s}"
      (json_indexed_kind column.kind)
      (json_z_number column.index)
  in
  let json_minimum_degree = function
    | None -> "null"
    | Some degree -> string_of_int (int_of_nat degree)
  in
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
      Printf.fprintf channel "  },\n";
      Printf.fprintf channel "  \"vk_metadata\": {\n";
      Printf.fprintf channel
        "    \"valid\": %s,\n" (json_bool metadata.valid);
      Printf.fprintf channel
        "    \"columns\": {\"advice\":%s,\"fixed\":%s,\"instance\":%s},\n"
        (json_z_number counts.advice)
        (json_z_number counts.fixed)
        (json_z_number counts.instance_);
      Printf.fprintf channel
        "    \"selector_types\": %s,\n"
        (json_inline_list json_bool metadata.selector_types);
      Printf.fprintf channel
        "    \"lookup_fixed_columns\": %s,\n"
        (json_inline_list json_z_number metadata.lookup_columns);
      Printf.fprintf channel
        "    \"advice_queries\": %s,\n"
        (json_inline_list json_query queries.advice);
      Printf.fprintf channel
        "    \"fixed_queries\": %s,\n"
        (json_inline_list json_query queries.fixed);
      Printf.fprintf channel
        "    \"instance_queries\": %s,\n"
        (json_inline_list json_query queries.instance_);
      Printf.fprintf channel
        "    \"permutation_columns\": %s,\n"
        (json_inline_list json_indexed_column metadata.permutation_columns);
      Printf.fprintf channel
        "    \"constants\": %s,\n"
        (json_inline_list json_z_number metadata.constants);
      Printf.fprintf channel
        "    \"minimum_degree\": %s\n"
        (json_minimum_degree metadata.minimum_degree);
      Printf.fprintf channel "  }\n";
      Printf.fprintf channel "}\n")

let () =
  match Array.to_list Sys.argv with
  | [_; "--structure"; structure_output] ->
      write_structure_json structure_output
  | [_; configure_output; synthesis_output] ->
      write_configure_json configure_output;
      write_synthesis_json synthesis_output
  | _ ->
      prerr_endline
        "usage: orchard_synthesis_json CONFIGURE.json SYNTHESIS.json\n\
         \       orchard_synthesis_json --structure STRUCTURE.json";
      exit 2
