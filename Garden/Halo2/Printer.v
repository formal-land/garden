Require Import Stdlib.Lists.List.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.Numbers.DecimalString.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Module PrettyPrint.
  Class C (T : Set) : Set := {
    to_string (value : T) (indent : Z) : string;
  }.

  Fixpoint indent_aux (indent : nat) : string :=
    match indent with
    | O => ""
    | S n => PrimString.cat (PrimString.make 1%int63 32%int63) (indent_aux n)
    end.

  Definition indent (indent : Z) : string :=
    indent_aux (Z.to_nat indent).

  Fixpoint cats (l : list string) : string :=
    match l with
    | [] => ""
    | x :: xs => PrimString.cat x (cats xs)
    end.

  Fixpoint separate (separator : string) (l : list string) : string :=
    match l with
    | [] => ""
    | [x] => x
    | x :: xs => cats [x; separator; separate separator xs]
    end.

  Definition endl : string := "
".

  Fixpoint pstring_of_uint (n : Decimal.uint) : string :=
    match n with
    | Decimal.Nil => ""
    | Decimal.D0 n => PrimString.cat (PrimString.make 1%int63 48%int63) (pstring_of_uint n)
    | Decimal.D1 n => PrimString.cat (PrimString.make 1%int63 49%int63) (pstring_of_uint n)
    | Decimal.D2 n => PrimString.cat (PrimString.make 1%int63 50%int63) (pstring_of_uint n)
    | Decimal.D3 n => PrimString.cat (PrimString.make 1%int63 51%int63) (pstring_of_uint n)
    | Decimal.D4 n => PrimString.cat (PrimString.make 1%int63 52%int63) (pstring_of_uint n)
    | Decimal.D5 n => PrimString.cat (PrimString.make 1%int63 53%int63) (pstring_of_uint n)
    | Decimal.D6 n => PrimString.cat (PrimString.make 1%int63 54%int63) (pstring_of_uint n)
    | Decimal.D7 n => PrimString.cat (PrimString.make 1%int63 55%int63) (pstring_of_uint n)
    | Decimal.D8 n => PrimString.cat (PrimString.make 1%int63 56%int63) (pstring_of_uint n)
    | Decimal.D9 n => PrimString.cat (PrimString.make 1%int63 57%int63) (pstring_of_uint n)
    end.

  Definition of_N (n : N) : string :=
    pstring_of_uint (N.to_uint n).

  Definition of_Z (z : Z) : string :=
    match z with
    | Z0 => "0"
    | Zpos p => of_N (N.pos p)
    | Zneg p => cats ["-"; of_N (N.pos p)]
    end.
End PrettyPrint.

Global Instance StringIsPrettyPrint : PrettyPrint.C string := {
  to_string self indent := PrettyPrint.cats [PrettyPrint.indent indent; self];
}.

Global Instance ListIsPrettyPrint {T : Set} `{PrettyPrint.C T} : PrettyPrint.C (list T) := {
  to_string self indent :=
    PrettyPrint.separate PrettyPrint.endl (
      List.map (fun item => PrettyPrint.to_string item indent) self
    );
}.

Module Halo2Pretty.
  Definition bool_to_string (b : bool) : string :=
    if b then "true" else "false".

  Definition line (indent : Z) (text : string) : string :=
    PrettyPrint.cats [PrettyPrint.indent indent; text].

  Definition field (indent : Z) (name value : string) : string :=
    PrettyPrint.cats [PrettyPrint.indent indent; name; ": "; value].

  Fixpoint join_lines (lines : list string) : string :=
    match lines with
    | [] => ""
    | [x] => x
    | x :: xs => PrettyPrint.cats [x; PrettyPrint.endl; join_lines xs]
    end.

  Definition block (indent : Z) (title : string) (items : list string) : string :=
    match items with
    | [] => line indent title
    | _ =>
      PrettyPrint.cats [
        line indent title;
        PrettyPrint.endl;
        join_lines items
      ]
    end.

  Definition print_option {A : Set} `{PrettyPrint.C A}
      (none_text : string) (value : option A) (indent : Z) : string :=
    match value with
    | Some x => PrettyPrint.to_string x indent
    | None => line indent none_text
    end.
End Halo2Pretty.

Global Instance ColumnKindIsPrettyPrint : PrettyPrint.C ColumnKind.t := {
  to_string self indent :=
    Halo2Pretty.line indent (
      match self with
      | ColumnKind.Advice => "advice"
      | ColumnKind.Fixed => "fixed"
      | ColumnKind.Instance => "instance"
      | ColumnKind.LookupTable => "lookup_table"
      end
    );
}.

Global Instance ColumnIsPrettyPrint : PrettyPrint.C Column.t := {
  to_string self indent :=
    PrettyPrint.cats [
      PrettyPrint.indent indent;
      self.(Column.label);
      " {kind=";
      PrettyPrint.to_string self.(Column.kind) 0;
      ", index=";
      PrettyPrint.of_Z self.(Column.index);
      "}"
    ];
}.

Global Instance SelectorIsPrettyPrint : PrettyPrint.C Selector.t := {
  to_string self indent :=
    PrettyPrint.cats [
      PrettyPrint.indent indent;
      self.(Selector.label);
      " {index=";
      PrettyPrint.of_Z self.(Selector.index);
      ", complex=";
      Halo2Pretty.bool_to_string self.(Selector.complex);
      "}"
    ];
}.

Global Instance RotationIsPrettyPrint : PrettyPrint.C Rotation.t := {
  to_string self indent :=
    Halo2Pretty.line indent (
      match self with
      | Rotation.Cur => "cur"
      | Rotation.Prev => "prev"
      | Rotation.Next => "next"
      | Rotation.At offset =>
        PrettyPrint.cats ["at("; PrettyPrint.of_Z offset; ")"]
      end
    );
}.

Global Instance QueryIsPrettyPrint : PrettyPrint.C Query.t := {
  to_string self indent :=
    match self with
    | Query.Advice column rotation =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "advice(";
        PrettyPrint.to_string column 0;
        ", ";
        PrettyPrint.to_string rotation 0;
        ")"
      ]
    | Query.Fixed column rotation =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "fixed(";
        PrettyPrint.to_string column 0;
        ", ";
        PrettyPrint.to_string rotation 0;
        ")"
      ]
    | Query.Instance column rotation =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "instance(";
        PrettyPrint.to_string column 0;
        ", ";
        PrettyPrint.to_string rotation 0;
        ")"
      ]
    | Query.Selector selector =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "selector(";
        PrettyPrint.to_string selector 0;
        ")"
      ]
    | Query.Challenge name =>
      PrettyPrint.cats [PrettyPrint.indent indent; "challenge("; name; ")"]
    | Query.NamedCell name =>
      PrettyPrint.cats [PrettyPrint.indent indent; "cell("; name; ")"]
    end;
}.

Fixpoint string_of_expr (self : Expr.t) (indent : Z) : string :=
  match self with
  | Expr.Constant value =>
    PrettyPrint.cats [PrettyPrint.indent indent; PrettyPrint.of_Z value]
  | Expr.Query query =>
    PrettyPrint.to_string query indent
  | Expr.Add x y =>
    Halo2Pretty.block indent "Add" [
      string_of_expr x (indent + 2);
      string_of_expr y (indent + 2)
    ]
  | Expr.Sub x y =>
    Halo2Pretty.block indent "Sub" [
      string_of_expr x (indent + 2);
      string_of_expr y (indent + 2)
    ]
  | Expr.Neg x =>
    Halo2Pretty.block indent "Neg" [
      string_of_expr x (indent + 2)
    ]
  | Expr.Mul x y =>
    Halo2Pretty.block indent "Mul" [
      string_of_expr x (indent + 2);
      string_of_expr y (indent + 2)
    ]
  | Expr.Named name body =>
    Halo2Pretty.block indent (PrettyPrint.cats ["Named "; name]) [
      string_of_expr body (indent + 2)
    ]
  end.

Global Instance ExprIsPrettyPrint : PrettyPrint.C Expr.t := {
  to_string := string_of_expr;
}.

Global Instance GateConstraintIsPrettyPrint : PrettyPrint.C GateConstraint.t := {
  to_string self indent :=
    Halo2Pretty.block indent self.(GateConstraint.name) [
      PrettyPrint.to_string self.(GateConstraint.expression) (indent + 2)
    ];
}.

Global Instance GateIsPrettyPrint : PrettyPrint.C Gate.t := {
  to_string self indent :=
    Halo2Pretty.block indent (PrettyPrint.cats ["gate "; self.(Gate.name)]) (
      [
        PrettyPrint.cats [
          PrettyPrint.indent (indent + 2);
          "selector: ";
          match self.(Gate.selector) with
          | Some selector => PrettyPrint.to_string selector 0
          | None => "none"
          end
        ];
        Halo2Pretty.line (indent + 2) "constraints:"
      ] ++
      List.map (fun constraint =>
        PrettyPrint.to_string constraint (indent + 4)
      ) self.(Gate.constraints)
    );
}.

Global Instance LookupPairIsPrettyPrint : PrettyPrint.C Lookup.pair := {
  to_string self indent :=
    Halo2Pretty.block indent "lookup pair" [
      Halo2Pretty.line (indent + 2) "input:";
      PrettyPrint.to_string self.(Lookup.input) (indent + 4);
      PrettyPrint.cats [
        PrettyPrint.indent (indent + 2);
        "table: ";
        PrettyPrint.to_string self.(Lookup.table) 0
      ]
    ];
}.

Global Instance LookupIsPrettyPrint : PrettyPrint.C Lookup.t := {
  to_string self indent :=
    Halo2Pretty.block indent (PrettyPrint.cats ["lookup "; self.(Lookup.name)]) (
      [
        PrettyPrint.cats [
          PrettyPrint.indent (indent + 2);
          "selector: ";
          match self.(Lookup.selector) with
          | Some selector => PrettyPrint.to_string selector 0
          | None => "none"
          end
        ];
        Halo2Pretty.line (indent + 2) "pairs:"
      ] ++
      List.map (fun pair => PrettyPrint.to_string pair (indent + 4)) self.(Lookup.pairs)
    );
}.

Global Instance ConfigEventIsPrettyPrint : PrettyPrint.C Config.Event.t := {
  to_string self indent :=
    match self with
    | Config.Event.AdviceColumn column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "advice_column ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.FixedColumn column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "fixed_column ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.InstanceColumn column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "instance_column ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.LookupTableColumn column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "lookup_table_column ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.Selector selector =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "selector ";
        PrettyPrint.to_string selector 0
      ]
    | Config.Event.EnableEquality column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "enable_equality ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.EnableConstant column =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "enable_constant ";
        PrettyPrint.to_string column 0
      ]
    | Config.Event.CreateGate gate =>
      PrettyPrint.to_string gate indent
    | Config.Event.CreateLookup lookup =>
      PrettyPrint.to_string lookup indent
    | Config.Event.ConfigureChip chip_name summary dependencies =>
      Halo2Pretty.block indent (PrettyPrint.cats ["configure_chip "; chip_name]) [
        Halo2Pretty.field (indent + 2) "summary" summary;
        Halo2Pretty.line (indent + 2) "dependencies:";
        PrettyPrint.to_string dependencies (indent + 4)
      ]
    end;
}.

Global Instance ConfigTraceIsPrettyPrint : PrettyPrint.C Config.Trace := {
  to_string self indent :=
    Halo2Pretty.block indent "configure" (
      List.map (fun event => PrettyPrint.to_string event (indent + 2)) self
    );
}.

Global Instance CellRefIsPrettyPrint : PrettyPrint.C CellRef.t := {
  to_string self indent :=
    PrettyPrint.cats [
      PrettyPrint.indent indent;
      self.(CellRef.name);
      match self.(CellRef.column) with
      | Some column =>
        PrettyPrint.cats [" @ "; PrettyPrint.to_string column 0]
      | None => ""
      end;
      match self.(CellRef.row) with
      | Some row =>
        PrettyPrint.cats [" row "; PrettyPrint.of_Z row]
      | None => ""
      end
    ];
}.

Global Instance RegionEventIsPrettyPrint : PrettyPrint.C RegionEvent.t := {
  to_string self indent :=
    match self with
    | RegionEvent.EnableSelector selector offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "enable_selector ";
        PrettyPrint.to_string selector 0;
        " @";
        PrettyPrint.of_Z offset
      ]
    | RegionEvent.AssignAdvice annotation column offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "assign_advice ";
        PrettyPrint.to_string column 0;
        " @";
        PrettyPrint.of_Z offset;
        " ; annotation=""";
        annotation;
        """"
      ]
    | RegionEvent.AssignFixed annotation column offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "assign_fixed ";
        PrettyPrint.to_string column 0;
        " @";
        PrettyPrint.of_Z offset;
        " ; annotation=""";
        annotation;
        """"
      ]
    | RegionEvent.AssignAdviceFromInstance annotation instance_column instance_row advice_column offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "assign_advice_from_instance ";
        PrettyPrint.to_string instance_column 0;
        "[";
        PrettyPrint.of_Z instance_row;
        "] -> ";
        PrettyPrint.to_string advice_column 0;
        " @";
        PrettyPrint.of_Z offset;
        " ; annotation=""";
        annotation;
        """"
      ]
    | RegionEvent.CopyAdvice annotation source column offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "copy_advice ";
        PrettyPrint.to_string source 0;
        " -> ";
        PrettyPrint.to_string column 0;
        " @";
        PrettyPrint.of_Z offset;
        " ; annotation=""";
        annotation;
        """"
      ]
    | RegionEvent.ConstrainEqual annotation lhs rhs =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "constrain_equal ";
        PrettyPrint.to_string lhs 0;
        " = ";
        PrettyPrint.to_string rhs 0;
        " ; annotation=""";
        annotation;
        """"
      ]
    | RegionEvent.Note message =>
      PrettyPrint.cats [PrettyPrint.indent indent; "note "; message]
    end;
}.

Global Instance TableEventIsPrettyPrint : PrettyPrint.C TableEvent.t := {
  to_string self indent :=
    match self with
    | TableEvent.AssignCell annotation column offset =>
      PrettyPrint.cats [
        PrettyPrint.indent indent; "assign_cell ";
        PrettyPrint.to_string column 0;
        " @";
        PrettyPrint.of_Z offset;
        " ; annotation=""";
        annotation;
        """"
      ]
    | TableEvent.Note message =>
      PrettyPrint.cats [PrettyPrint.indent indent; "note "; message]
    end;
}.

Fixpoint string_of_synth_event (self : Synth.Event.t) (indent : Z) : string :=
  match self with
  | Synth.Event.Namespace name events =>
    Halo2Pretty.block indent (PrettyPrint.cats ["namespace "; name]) (
      List.map (fun event => string_of_synth_event event (indent + 2)) events
    )
  | Synth.Event.Region name events =>
    Halo2Pretty.block indent (PrettyPrint.cats ["region "; name]) (
      List.map (fun event => PrettyPrint.to_string event (indent + 2)) events
    )
  | Synth.Event.Table name events =>
    Halo2Pretty.block indent (PrettyPrint.cats ["table "; name]) (
      List.map (fun event => PrettyPrint.to_string event (indent + 2)) events
    )
  | Synth.Event.LoadTable name =>
    PrettyPrint.cats [PrettyPrint.indent indent; "load_table "; name]
  | Synth.Event.ConstructChip name =>
    PrettyPrint.cats [PrettyPrint.indent indent; "construct_chip "; name]
  | Synth.Event.ConstrainInstance annotation cell instance_column row =>
    PrettyPrint.cats [
      PrettyPrint.indent indent; "constrain_instance ";
      PrettyPrint.to_string cell 0;
      " = ";
      PrettyPrint.to_string instance_column 0;
      "[";
      PrettyPrint.of_Z row;
      "] ; annotation=""";
      annotation;
      """"
    ]
  | Synth.Event.ConstrainEqual annotation lhs rhs =>
    PrettyPrint.cats [
      PrettyPrint.indent indent; "constrain_equal ";
      PrettyPrint.to_string lhs 0;
      " = ";
      PrettyPrint.to_string rhs 0;
      " ; annotation=""";
      annotation;
      """"
    ]
  | Synth.Event.Call name arguments =>
    Halo2Pretty.block indent (PrettyPrint.cats ["call "; name]) [
      PrettyPrint.to_string arguments (indent + 2)
    ]
  | Synth.Event.Witness name kind =>
    PrettyPrint.cats [PrettyPrint.indent indent; "witness "; name; " : "; kind]
  | Synth.Event.Return name =>
    PrettyPrint.cats [PrettyPrint.indent indent; "return "; name]
  | Synth.Event.Note message =>
    PrettyPrint.cats [PrettyPrint.indent indent; "note "; message]
  end.

Global Instance SynthEventIsPrettyPrint : PrettyPrint.C Synth.Event.t := {
  to_string := string_of_synth_event;
}.

Global Instance SynthTraceIsPrettyPrint : PrettyPrint.C Synth.Trace := {
  to_string self indent :=
    Halo2Pretty.block indent "synthesize" (
      List.map (fun event => PrettyPrint.to_string event (indent + 2)) self
    );
}.

Global Instance ChipIsPrettyPrint : PrettyPrint.C Chip.t := {
  to_string self indent :=
    Halo2Pretty.block indent (PrettyPrint.cats ["chip "; self.(Chip.name)]) [
      Halo2Pretty.field (indent + 2) "config" self.(Chip.config_name);
      Halo2Pretty.line (indent + 2) "dependencies:";
      PrettyPrint.to_string self.(Chip.dependencies) (indent + 4);
      PrettyPrint.to_string self.(Chip.configure) (indent + 2);
      PrettyPrint.to_string self.(Chip.synthesize) (indent + 2)
    ];
}.

Global Instance CircuitIsPrettyPrint : PrettyPrint.C Circuit.t := {
  to_string self indent :=
    Halo2Pretty.block indent (PrettyPrint.cats ["circuit "; self.(Circuit.name)]) [
      Halo2Pretty.line (indent + 2) "dependencies:";
      PrettyPrint.to_string self.(Circuit.dependencies) (indent + 4);
      PrettyPrint.to_string self.(Circuit.configure) (indent + 2);
      PrettyPrint.to_string self.(Circuit.synthesize) (indent + 2)
    ];
}.
