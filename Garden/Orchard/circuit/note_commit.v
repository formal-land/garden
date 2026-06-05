Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
Require Import Garden.Halo2.DSL.
Require Import Garden.Halo2.Gadgets.Ecc.
Require Import Garden.Halo2.Gadgets.LookupRangeCheck.
Require Import Garden.Halo2.Gadgets.Sinsemilla.
Require Import Garden.Orchard.constants.

Import ListNotations.
Export PStringNotations.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.

Definition helper_gate (name summary : string) (selector : Selector.t) : Gate.t :=
  Gate.make
    name
    (Some selector)
    [GateConstraint.make summary (Expr.Named summary (Expr.named_cell name))].

Definition helper_assign (name summary : string) (selector : Selector.t) : Synth.Event.t :=
  Synth.Event.Region name [
    RegionEvent.EnableSelector selector 0;
    RegionEvent.Note summary
  ].

Module NoteCommitConfig.
  Record t : Set := {
    advices : list Column.t;
    sinsemilla_config_name : string;
    q_b : Selector.t;
    q_d : Selector.t;
    q_e : Selector.t;
    q_g : Selector.t;
    q_h : Selector.t;
    q_gd : Selector.t;
    q_pkd : Selector.t;
    q_value : Selector.t;
    q_rho : Selector.t;
    q_psi : Selector.t;
    q_y : Selector.t;
  }.
End NoteCommitConfig.

Module DecomposeB.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate
      "NoteCommit MessagePiece b"
      "b = b_0 + 2^10 b_1 + 2^20 b_2 + 2^30 b_3"
      cfg.(NoteCommitConfig.q_b).

  Definition decompose (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "b" [
      Synth.Event.Call "DecomposeB::decompose" ["g_d"; "pk_d"];
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "b_0";
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "b_3";
      helper_assign "NoteCommit MessagePiece b" "assign b_1 and b_2 and constrain the b piece" cfg.(NoteCommitConfig.q_b);
      Synth.Event.Return "b"
    ].
End DecomposeB.

Module DecomposeD.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate
      "NoteCommit MessagePiece d"
      "d = d_0 + 2^10 d_1 + 2^20 d_2 with carry z1_d"
      cfg.(NoteCommitConfig.q_d).

  Definition decompose (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "d" [
      Synth.Event.Call "DecomposeD::decompose" ["pk_d"; "value"];
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "d_2";
      helper_assign "NoteCommit MessagePiece d" "assign d_0, d_1, d_2 and z1_d" cfg.(NoteCommitConfig.q_d);
      Synth.Event.Return "d"
    ].
End DecomposeD.

Module DecomposeE.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate
      "NoteCommit MessagePiece e"
      "e = e_0 + 2^10 e_1"
      cfg.(NoteCommitConfig.q_e).

  Definition decompose (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "e" [
      Synth.Event.Call "DecomposeE::decompose" ["value"; "rho"];
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "e_0";
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "e_1";
      helper_assign "NoteCommit MessagePiece e" "assign e_0 and e_1" cfg.(NoteCommitConfig.q_e);
      Synth.Event.Return "e"
    ].
End DecomposeE.

Module DecomposeG.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate
      "NoteCommit MessagePiece g"
      "g = g_0 + 2^10 g_1 with carry z1_g"
      cfg.(NoteCommitConfig.q_g).

  Definition decompose (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "g" [
      Synth.Event.Call "DecomposeG::decompose" ["rho"; "psi"];
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "g_1";
      helper_assign "NoteCommit MessagePiece g" "assign g_0, g_1 and z1_g" cfg.(NoteCommitConfig.q_g);
      Synth.Event.Return "g"
    ].
End DecomposeG.

Module DecomposeH.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate
      "NoteCommit MessagePiece h"
      "h = h_0 + 2^10 h_1"
      cfg.(NoteCommitConfig.q_h).

  Definition decompose (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "h" [
      Synth.Event.Call "DecomposeH::decompose" ["psi"];
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "h_0";
      helper_assign "NoteCommit MessagePiece h" "assign h_1 and constrain final psi piece" cfg.(NoteCommitConfig.q_h);
      Synth.Event.Return "h"
    ].
End DecomposeH.

Module GdCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "NoteCommit input g_d" "g_d x-coordinate canonicity limbs" cfg.(NoteCommitConfig.q_gd).

  Definition assign (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    helper_assign "NoteCommit input g_d" "assign g_d canonicity witnesses" cfg.(NoteCommitConfig.q_gd).
End GdCanonicity.

Module PkdCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "NoteCommit input pk_d" "pk_d x-coordinate canonicity limbs" cfg.(NoteCommitConfig.q_pkd).

  Definition assign (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    helper_assign "NoteCommit input pk_d" "assign pk_d canonicity witnesses" cfg.(NoteCommitConfig.q_pkd).
End PkdCanonicity.

Module ValueCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "NoteCommit input value" "64-bit note value decomposition" cfg.(NoteCommitConfig.q_value).

  Definition assign (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    helper_assign "NoteCommit input value" "assign value canonicity witnesses" cfg.(NoteCommitConfig.q_value).
End ValueCanonicity.

Module RhoCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "NoteCommit input rho" "rho canonicity limbs" cfg.(NoteCommitConfig.q_rho).

  Definition assign (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    helper_assign "NoteCommit input rho" "assign rho canonicity witnesses" cfg.(NoteCommitConfig.q_rho).
End RhoCanonicity.

Module PsiCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "NoteCommit input psi" "psi canonicity limbs" cfg.(NoteCommitConfig.q_psi).

  Definition assign (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    helper_assign "NoteCommit input psi" "assign psi canonicity witnesses" cfg.(NoteCommitConfig.q_psi).
End PsiCanonicity.

Module YCanonicity.
  Definition gate (cfg : NoteCommitConfig.t) : Gate.t :=
    helper_gate "y coordinate checks" "y-coordinate LSB and canonical encoding checks" cfg.(NoteCommitConfig.q_y).

  Definition assign (cfg : NoteCommitConfig.t) (name : string) : Synth.Event.t :=
    Synth.Event.Namespace name [
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "k_0";
      LookupRangeCheck.witness_check
        {|
          LookupRangeCheckConfig.q_lookup := Selector.complex_selector 0 "q_lookup";
          LookupRangeCheckConfig.advice := Column.advice 9 "range_check";
          LookupRangeCheckConfig.table_idx := Column.lookup_table 0 "table_idx";
          LookupRangeCheckConfig.bits := 10;
        |}
        "k_2";
      helper_assign "y coordinate checks" "assign LSB and y-coordinate canonicity witnesses" cfg.(NoteCommitConfig.q_y);
      Synth.Event.Return name
    ].
End YCanonicity.

Module NoteCommitChip.
  Record t : Set := {
    config : NoteCommitConfig.t;
  }.

  Definition configure
      (selector_base : Z)
      (advices : list Column.t)
      (sinsemilla_config_name : string)
      : NoteCommitConfig.t * Config.Trace :=
    let cfg := {|
      NoteCommitConfig.advices := advices;
      NoteCommitConfig.sinsemilla_config_name := sinsemilla_config_name;
      NoteCommitConfig.q_b := Selector.make selector_base "q_note_commit_b";
      NoteCommitConfig.q_d := Selector.make (selector_base + 1) "q_note_commit_d";
      NoteCommitConfig.q_e := Selector.make (selector_base + 2) "q_note_commit_e";
      NoteCommitConfig.q_g := Selector.make (selector_base + 3) "q_note_commit_g";
      NoteCommitConfig.q_h := Selector.make (selector_base + 4) "q_note_commit_h";
      NoteCommitConfig.q_gd := Selector.make (selector_base + 5) "q_note_commit_gd";
      NoteCommitConfig.q_pkd := Selector.make (selector_base + 6) "q_note_commit_pkd";
      NoteCommitConfig.q_value := Selector.make (selector_base + 7) "q_note_commit_value";
      NoteCommitConfig.q_rho := Selector.make (selector_base + 8) "q_note_commit_rho";
      NoteCommitConfig.q_psi := Selector.make (selector_base + 9) "q_note_commit_psi";
      NoteCommitConfig.q_y := Selector.make (selector_base + 10) "q_note_commit_y";
    |} in
    (cfg,
    [
      Config.Event.Selector cfg.(NoteCommitConfig.q_b);
      Config.Event.Selector cfg.(NoteCommitConfig.q_d);
      Config.Event.Selector cfg.(NoteCommitConfig.q_e);
      Config.Event.Selector cfg.(NoteCommitConfig.q_g);
      Config.Event.Selector cfg.(NoteCommitConfig.q_h);
      Config.Event.Selector cfg.(NoteCommitConfig.q_gd);
      Config.Event.Selector cfg.(NoteCommitConfig.q_pkd);
      Config.Event.Selector cfg.(NoteCommitConfig.q_value);
      Config.Event.Selector cfg.(NoteCommitConfig.q_rho);
      Config.Event.Selector cfg.(NoteCommitConfig.q_psi);
      Config.Event.Selector cfg.(NoteCommitConfig.q_y);
      Config.Event.ConfigureChip
        "NoteCommitChip"
        "decomposition and canonicity checking for Orchard note commitments"
        [
          "orchard::circuit::note_commit";
          "halo2_gadgets::sinsemilla";
          "halo2_gadgets::ecc";
          "halo2_gadgets::utilities::lookup_range_check"
        ];
      Config.Event.CreateGate (DecomposeB.gate cfg);
      Config.Event.CreateGate (DecomposeD.gate cfg);
      Config.Event.CreateGate (DecomposeE.gate cfg);
      Config.Event.CreateGate (DecomposeG.gate cfg);
      Config.Event.CreateGate (DecomposeH.gate cfg);
      Config.Event.CreateGate (GdCanonicity.gate cfg);
      Config.Event.CreateGate (PkdCanonicity.gate cfg);
      Config.Event.CreateGate (ValueCanonicity.gate cfg);
      Config.Event.CreateGate (RhoCanonicity.gate cfg);
      Config.Event.CreateGate (PsiCanonicity.gate cfg);
      Config.Event.CreateGate (YCanonicity.gate cfg)
    ]).

  Definition construct (cfg : NoteCommitConfig.t) : t := {|
    config := cfg;
  |}.
End NoteCommitChip.

Module Gadgets.
  Definition note_commit (cfg : NoteCommitConfig.t) : Synth.Event.t :=
    Synth.Event.Namespace "Hash NoteCommit pieces" [
      Synth.Event.Call
        "gadgets::note_commit"
        ["g_d"; "pk_d"; "value"; "rho"; "psi"; "rcm"];
      Synth.Event.Namespace "Process NoteCommit inputs" [
        Synth.Event.Call
          "MessagePiece::from_components"
          ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"]
      ];
      Synth.Event.Call "extract a from y(g_d)" ["g_d"];
      DecomposeB.decompose cfg;
      Synth.Event.Call "derive c from x(pk_d)" ["pk_d"];
      DecomposeD.decompose cfg;
      DecomposeE.decompose cfg;
      Synth.Event.Call "derive f from rho" ["rho"];
      DecomposeG.decompose cfg;
      DecomposeH.decompose cfg;
      YCanonicity.assign cfg "y(g_d) decomposition";
      YCanonicity.assign cfg "y(pk_d) decomposition";
      GdCanonicity.assign cfg;
      PkdCanonicity.assign cfg;
      ValueCanonicity.assign cfg;
      RhoCanonicity.assign cfg;
      PsiCanonicity.assign cfg;
      Synth.Event.Namespace "x(g_d) canonicity" [
        Synth.Event.Note "13 ten-bit lookups for x(g_d)"
      ];
      Synth.Event.Namespace "x(pk_d) canonicity" [
        Synth.Event.Note "13 ten-bit lookups for x(pk_d)"
      ];
      Synth.Event.Namespace "rho canonicity" [
        Synth.Event.Note "13 ten-bit lookups for rho"
      ];
      Synth.Event.Namespace "psi canonicity" [
        Synth.Event.Note "13 ten-bit lookups for psi"
      ];
      Sinsemilla.commit
        "Sinsemilla NoteCommit"
        Domain.NoteCommit
        "g_d || pk_d || i2lebsp_64(value) || i2lebsp_255(rho) || i2lebsp_255(psi)"
        FixedBase.NoteCommitR;
      Ecc.fixed_mul "[rcm] NoteCommitR" FixedBase.NoteCommitR "rcm";
      Ecc.add "cm" "Sinsemilla NoteCommit" "[rcm] NoteCommitR";
      Synth.Event.Return "cm"
    ].
End Gadgets.

Definition as_chip (cfg : NoteCommitConfig.t) : Chip.t := {|
  Chip.name := "NoteCommitChip";
  Chip.config_name := "NoteCommitConfig";
  Chip.dependencies := ["SinsemillaChip"; "EccChip"; "LookupRangeCheck"];
  Chip.configure := [
    Config.Event.CreateGate (DecomposeB.gate cfg);
    Config.Event.CreateGate (DecomposeD.gate cfg);
    Config.Event.CreateGate (DecomposeE.gate cfg);
    Config.Event.CreateGate (DecomposeG.gate cfg);
    Config.Event.CreateGate (DecomposeH.gate cfg);
    Config.Event.CreateGate (GdCanonicity.gate cfg);
    Config.Event.CreateGate (PkdCanonicity.gate cfg);
    Config.Event.CreateGate (ValueCanonicity.gate cfg);
    Config.Event.CreateGate (RhoCanonicity.gate cfg);
    Config.Event.CreateGate (PsiCanonicity.gate cfg);
    Config.Event.CreateGate (YCanonicity.gate cfg)
  ];
  Chip.synthesize := [Gadgets.note_commit cfg];
|}.
