(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module Window4Signals.
  Record t : Set := {
    in_ : list F.t;
    base : list F.t;
    out : list F.t;
    out8 : list F.t;
  }.
End Window4Signals.

(* Template body *)
Definition Window4 : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ 4 ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "base" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out8" [[ [ 2 ] ]] in
  (* Component *)
  do~ M.declare_component "mux" in
  do~ M.substitute_var "mux" [[ M.call_function ~(| "MultiMux3", [ 2 ] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "in", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "in", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "in", [Access.Array (2)] |) ]] in
  (* Component *)
  do~ M.declare_component "dbl2" in
  do~ M.substitute_var "dbl2" [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr3" in
  do~ M.substitute_var "adr3" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr4" in
  do~ M.substitute_var "adr4" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr5" in
  do~ M.substitute_var "adr5" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr6" in
  do~ M.substitute_var "adr6" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr7" in
  do~ M.substitute_var "adr7" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  (* Component *)
  do~ M.declare_component "adr8" in
  do~ M.substitute_var "adr8" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "dbl2" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "dbl2" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "dbl2", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "dbl2", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr3" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr3" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr3" [[ M.var_access ~(| "dbl2", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr3" [[ M.var_access ~(| "dbl2", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr3", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr3", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr4" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr4" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr4" [[ M.var_access ~(| "adr3", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr4" [[ M.var_access ~(| "adr3", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr4", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr4", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr5" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr5" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr5" [[ M.var_access ~(| "adr4", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr5" [[ M.var_access ~(| "adr4", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr5", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr5", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr6" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr6" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr6" [[ M.var_access ~(| "adr5", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr6" [[ M.var_access ~(| "adr5", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr6", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr6", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr7" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr7" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr7" [[ M.var_access ~(| "adr6", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr7" [[ M.var_access ~(| "adr6", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr7", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr7", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr8" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr8" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  do~ M.substitute_var "adr8" [[ M.var_access ~(| "adr7", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "adr8" [[ M.var_access ~(| "adr7", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr8", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "mux" [[ M.var_access ~(| "adr8", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "out8" [[ M.var_access ~(| "adr8", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "out8" [[ M.var_access ~(| "adr8", [Access.Component "out"; Access.Array (1)] |) ]] in
  do~ M.substitute_var "out" [[ M.var_access ~(| "mux", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "out" [[ InfixOp.add ~(| InfixOp.mul ~(| InfixOp.mul ~(| PrefixOp.sub ~(| M.var_access ~(| "mux", [Access.Component "out"; Access.Array (1)] |) |), 2 |), M.var_access ~(| "in", [Access.Array (3)] |) |), M.var_access ~(| "mux", [Access.Component "out"; Access.Array (1)] |) |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module SegmentSignals.
  Record t : Set := {
    in_ : list F.t;
    base : list F.t;
    out : list F.t;
  }.
End SegmentSignals.

(* Template body *)
Definition Segment (nWindows : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ InfixOp.mul ~(| M.var ~(| "nWindows" |), 4 |) ] ]] in
  (* Signal Input *)
  do~ M.declare_signal "base" [[ [ 2 ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "j" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "j" [[ 0 ]] in
  (* Component *)
  do~ M.declare_component "e2m" in
  do~ M.substitute_var "e2m" [[ M.call_function ~(| "Edwards2Montgomery", ([] : list F.t) |) ]] in
  do~ M.substitute_var "e2m" [[ M.var_access ~(| "base", [Access.Array (0)] |) ]] in
  do~ M.substitute_var "e2m" [[ M.var_access ~(| "base", [Access.Array (1)] |) ]] in
  (* Component *)
  do~ M.declare_component "windows" in
  (* Component *)
  do~ M.declare_component "doublers1" in
  (* Component *)
  do~ M.declare_component "doublers2" in
  (* Component *)
  do~ M.declare_component "adders" in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "nWindows" |) |) ]] (
    do~ M.substitute_var "windows" [[ M.call_function ~(| "Window4", ([] : list F.t) |) ]] in
    do~ M.substitute_var "j" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "j" |), 4 |) ]] (
      do~ M.substitute_var "windows" [[ M.var_access ~(| "in", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 4, M.var ~(| "i" |) |), M.var ~(| "j" |) |))] |) ]] in
      do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var ~(| "j" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "i" |), 0 |) ]] (* then *) (
      do~ M.substitute_var "windows" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "windows" [[ M.var_access ~(| "e2m", [Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.substitute_var "doublers1" [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
      do~ M.substitute_var "doublers2" [[ M.call_function ~(| "MontgomeryDouble", ([] : list F.t) |) ]] in
      do~ M.substitute_var "doublers1" [[ M.var_access ~(| "windows", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out8"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "doublers1" [[ M.var_access ~(| "windows", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out8"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "doublers2" [[ M.var_access ~(| "doublers1", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "doublers2" [[ M.var_access ~(| "doublers1", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "windows" [[ M.var_access ~(| "doublers2", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "windows" [[ M.var_access ~(| "doublers2", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "adders" [[ M.call_function ~(| "MontgomeryAdd", ([] : list F.t) |) ]] in
      do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "i" |), 1 |) ]] (* then *) (
        do~ M.substitute_var "adders" [[ M.var_access ~(| "windows", [Access.Array (0); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [[ M.var_access ~(| "windows", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 2 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 2 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "windows", [Access.Array (M.var ~(| "i" |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "windows", [Access.Array (M.var ~(| "i" |)); Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "m2e" in
  do~ M.substitute_var "m2e" [[ M.call_function ~(| "Montgomery2Edwards", ([] : list F.t) |) ]] in
  do~ M.if_ [[ InfixOp.greater ~(| M.var ~(| "nWindows" |), 1 |) ]] (* then *) (
    do~ M.substitute_var "m2e" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nWindows" |), 2 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "m2e" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nWindows" |), 2 |)); Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ) (* else *) (
    do~ M.substitute_var "m2e" [[ M.var_access ~(| "windows", [Access.Array (0); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "m2e" [[ M.var_access ~(| "windows", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.substitute_var "out" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (0)] |) ]] in
  do~ M.substitute_var "out" [[ M.var_access ~(| "m2e", [Access.Component "out"; Access.Array (1)] |) ]] in
  M.pure BlockUnit.Tt.

(* Template signals *)
Module PedersenSignals.
  Record t : Set := {
    in_ : list F.t;
    out : list F.t;
  }.
End PedersenSignals.

(* Template body *)
Definition Pedersen (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  (* Signal Input *)
  do~ M.declare_signal "in" [[ [ M.var ~(| "n" |) ] ]] in
  (* Signal Output *)
  do~ M.declare_signal "out" [[ [ 2 ] ]] in
  (* Var *)
  do~ M.declare_var "BASE" [[ [ 10; 2 ] ]] in
  do~ M.substitute_var "BASE" [[ array_with_repeat (array_with_repeat (0) (2)) (10) ]] in
  do~ M.substitute_var "BASE" [[ [ [ 10457101036533406547632367118273992217979173478358440826365724437999023779287; 19824078218392094440610104313265183977899662750282163392862422243483260492317 ]; [ 2671756056509184035029146175565761955751135805354291559563293617232983272177; 2663205510731142763556352975002641716101654201788071096152948830924149045094 ]; [ 5802099305472655231388284418920769829666717045250560929368476121199858275951; 5980429700218124965372158798884772646841287887664001482443826541541529227896 ]; [ 7107336197374528537877327281242680114152313102022415488494307685842428166594; 2857869773864086953506483169737724679646433914307247183624878062391496185654 ]; [ 20265828622013100949498132415626198973119240347465898028410217039057588424236; 1160461593266035632937973507065134938065359936056410650153315956301179689506 ]; [ 1487999857809287756929114517587739322941449154962237464737694709326309567994; 14017256862867289575056460215526364897734808720610101650676790868051368668003 ]; [ 14618644331049802168996997831720384953259095788558646464435263343433563860015; 13115243279999696210147231297848654998887864576952244320558158620692603342236 ]; [ 6814338563135591367010655964669793483652536871717891893032616415581401894627; 13660303521961041205824633772157003587453809761793065294055279768121314853695 ]; [ 3571615583211663069428808372184817973703476260057504149923239576077102575715; 11981351099832644138306422070127357074117642951423551606012551622164230222506 ]; [ 18597552580465440374022635246985743886550544261632147935254624835147509493269; 6753322320275422086923032033899357299485124665258735666995435957890214041481 ] ] ]] in
  (* Var *)
  do~ M.declare_var "nSegments" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nSegments" [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var ~(| "n" |), 1 |), 200 |), 1 |) ]] in
  (* Component *)
  do~ M.declare_component "segments" in
  (* Var *)
  do~ M.declare_var "i" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "j" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "j" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "nBits" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nBits" [[ 0 ]] in
  (* Var *)
  do~ M.declare_var "nWindows" [[ ([] : list F.t) ]] in
  do~ M.substitute_var "nWindows" [[ 0 ]] in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), M.var ~(| "nSegments" |) |) ]] (
    do~ M.substitute_var "nBits" [[ ternary_expression (InfixOp.eq ~(| M.var ~(| "i" |), InfixOp.sub ~(| M.var ~(| "nSegments" |), 1 |) |)) (InfixOp.sub ~(| M.var ~(| "n" |), InfixOp.mul ~(| InfixOp.sub ~(| M.var ~(| "nSegments" |), 1 |), 200 |) |)) (200) ]] in
    do~ M.substitute_var "nWindows" [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var ~(| "nBits" |), 1 |), 4 |), 1 |) ]] in
    do~ M.substitute_var "segments" [[ M.call_function ~(| "Segment", [ M.var ~(| "nWindows" |) ] |) ]] in
    do~ M.substitute_var "segments" [[ M.var_access ~(| "BASE", [Access.Array (M.var ~(| "i" |)); Access.Array (0)] |) ]] in
    do~ M.substitute_var "segments" [[ M.var_access ~(| "BASE", [Access.Array (M.var ~(| "i" |)); Access.Array (1)] |) ]] in
    do~ M.substitute_var "j" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "j" |), M.var ~(| "nBits" |) |) ]] (
      do~ M.substitute_var "segments" [[ M.var_access ~(| "in", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var ~(| "i" |), 200 |), M.var ~(| "j" |) |))] |) ]] in
      do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var ~(| "j" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "j" [[ M.var ~(| "nBits" |) ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "j" |), InfixOp.mul ~(| M.var ~(| "nWindows" |), 4 |) |) ]] (
      do~ M.substitute_var "segments" [[ 0 ]] in
      do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var ~(| "j" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  (* Component *)
  do~ M.declare_component "adders" in
  do~ M.substitute_var "i" [[ 0 ]] in
  do~ M.while [[ InfixOp.lesser ~(| M.var ~(| "i" |), InfixOp.sub ~(| M.var ~(| "nSegments" |), 1 |) |) ]] (
    do~ M.substitute_var "adders" [[ M.call_function ~(| "BabyAdd", ([] : list F.t) |) ]] in
    do~ M.if_ [[ InfixOp.eq ~(| M.var ~(| "i" |), 0 |) ]] (* then *) (
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (1); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (1); Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) (* else *) (
      do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "xout"] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "i" |), 1 |)); Access.Component "yout"] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.add ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
      do~ M.substitute_var "adders" [[ M.var_access ~(| "segments", [Access.Array (InfixOp.add ~(| M.var ~(| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var ~(| "i" |), 1 |) ]] in
    M.pure BlockUnit.Tt
  ) in
  do~ M.if_ [[ InfixOp.greater ~(| M.var ~(| "nSegments" |), 1 |) ]] (* then *) (
    do~ M.substitute_var "out" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nSegments" |), 2 |)); Access.Component "xout"] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access ~(| "adders", [Access.Array (InfixOp.sub ~(| M.var ~(| "nSegments" |), 2 |)); Access.Component "yout"] |) ]] in
    M.pure BlockUnit.Tt
  ) (* else *) (
    do~ M.substitute_var "out" [[ M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access ~(| "segments", [Access.Array (0); Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ) in
  M.pure BlockUnit.Tt.
