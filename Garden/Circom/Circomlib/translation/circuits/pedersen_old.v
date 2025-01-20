(* Generated by Garden *)
Require Import Garden.Garden.

(* Template signals *)
Module PedersenSignals.
  Record t : Set := {
    (* Input *)
    in_ : list F.t;
    (* Output *)
    out : list F.t;
  }.
End PedersenSignals.

(* Template body *)
Definition Pedersen (n : F.t) : M.t (BlockUnit.t Empty_set) :=
  M.template_body [("n", n)] (
    (* Signal Input *)
    do~ M.declare_signal "in" [[ [ M.var (| "n" |) ] ]] in
    (* Signal Output *)
    do~ M.declare_signal "out" [[ [ 2 ] ]] in
    (* Var *)
    do~ M.declare_var "nexps" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nexps" [[ InfixOp.add ~(| InfixOp.intDiv ~(| InfixOp.sub ~(| M.var (| "n" |), 1 |), 250 |), 1 |) ]] in
    (* Var *)
    do~ M.declare_var "nlastbits" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nlastbits" [[ InfixOp.sub ~(| M.var (| "n" |), InfixOp.mul ~(| InfixOp.sub ~(| M.var (| "nexps" |), 1 |), 250 |) |) ]] in
    (* Component *)
    do~ M.declare_component "escalarMuls" in
    (* Var *)
    do~ M.declare_var "PBASE" [[ [ 10; 2 ] ]] in
    do~ M.substitute_var "PBASE" [[ array_with_repeat (array_with_repeat (0) (2)) (10) ]] in
    do~ M.substitute_var "PBASE" [[ [ [ 10457101036533406547632367118273992217979173478358440826365724437999023779287; 19824078218392094440610104313265183977899662750282163392862422243483260492317 ]; [ 2671756056509184035029146175565761955751135805354291559563293617232983272177; 2663205510731142763556352975002641716101654201788071096152948830924149045094 ]; [ 5802099305472655231388284418920769829666717045250560929368476121199858275951; 5980429700218124965372158798884772646841287887664001482443826541541529227896 ]; [ 7107336197374528537877327281242680114152313102022415488494307685842428166594; 2857869773864086953506483169737724679646433914307247183624878062391496185654 ]; [ 20265828622013100949498132415626198973119240347465898028410217039057588424236; 1160461593266035632937973507065134938065359936056410650153315956301179689506 ]; [ 1487999857809287756929114517587739322941449154962237464737694709326309567994; 14017256862867289575056460215526364897734808720610101650676790868051368668003 ]; [ 14618644331049802168996997831720384953259095788558646464435263343433563860015; 13115243279999696210147231297848654998887864576952244320558158620692603342236 ]; [ 6814338563135591367010655964669793483652536871717891893032616415581401894627; 13660303521961041205824633772157003587453809761793065294055279768121314853695 ]; [ 3571615583211663069428808372184817973703476260057504149923239576077102575715; 11981351099832644138306422070127357074117642951423551606012551622164230222506 ]; [ 18597552580465440374022635246985743886550544261632147935254624835147509493269; 6753322320275422086923032033899357299485124665258735666995435957890214041481 ] ] ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "j" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "j" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "nexpbits" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "nexpbits" [[ 0 ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), M.var (| "nexps" |) |) ]] (
      do~ M.substitute_var "nexpbits" [[ ternary_expression (InfixOp.eq ~(| M.var (| "i" |), InfixOp.sub ~(| M.var (| "nexps" |), 1 |) |)) (M.var (| "nlastbits" |)) (250) ]] in
      do~ M.substitute_var "escalarMuls" [[ M.call_function ~(| "EscalarMul", [ M.var (| "nexpbits" |); M.var_access (| "PBASE", [Access.Array (M.var (| "i" |))] |) ] |) ]] in
      do~ M.substitute_var "j" [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), M.var (| "nexpbits" |) |) ]] (
        do~ M.substitute_var "escalarMuls" [[ M.var_access (| "in", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| 250, M.var (| "i" |) |), M.var (| "j" |) |))] |) ]] in
        do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.if_ [[ InfixOp.eq ~(| M.var (| "i" |), 0 |) ]] (* then *) (
        do~ M.substitute_var "escalarMuls" [[ 0 ]] in
        do~ M.substitute_var "escalarMuls" [[ 1 ]] in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "escalarMuls" [[ M.var_access (| "escalarMuls", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
        do~ M.substitute_var "escalarMuls" [[ M.var_access (| "escalarMuls", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "out" [[ M.var_access (| "escalarMuls", [Access.Array (InfixOp.sub ~(| M.var (| "nexps" |), 1 |)); Access.Component "out"; Access.Array (0)] |) ]] in
    do~ M.substitute_var "out" [[ M.var_access (| "escalarMuls", [Access.Array (InfixOp.sub ~(| M.var (| "nexps" |), 1 |)); Access.Component "out"; Access.Array (1)] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Template not under-constrained *)
Definition Pedersen_not_under_constrained (n : F.t) in_ : Prop :=
  exists! out,
  let signals := PedersenSignals.Build_t in_ out in
  True (* NotUnderConstrained Pedersen n signals *).
