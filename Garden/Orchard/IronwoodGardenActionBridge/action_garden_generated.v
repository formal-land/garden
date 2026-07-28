(** Generated from the axiom-free Lean ActionGarden.
    Lean source SHA-256: 731cb3b1ee03ad1a3f35e327aa0bc45078d551eaaff611610158719295131198

    This file is a declaration-for-declaration concrete mirror.  It uses [ActionGardenZ_Z]
    as its sole specification arithmetic carrier; [nat] occurs only as a
    structural recursion index, exactly as [Nat] does in the Lean source.
    Rocq's primitive [int] occurs only behind the checked accessor for the two
    generated immutable constant arrays. *)

From Stdlib Require Import ZArith List Bool Uint63 Array.PrimArray.
Require Export
  Garden.Orchard.IronwoodGardenActionBridge.action_garden_constants.
Import ListNotations.
Open Scope Z_scope.


Notation Not := not.

(** ** Explicit integer and field arithmetic

    [ActionGardenZ_Z] is an alias for Rocq's mathematical integers.  The [base*] and
    [scalar*] operations below always reduce modulo the named Pallas modulus;
    no coercion or type-class operation hides which field is in use. *)

Definition ActionGardenZ_Z : Type := BinNums.Z.

Definition ActionGardenZ_pallasBaseModulus : ActionGardenZ_Z :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337.

Definition ActionGardenZ_pallasScalarModulus : ActionGardenZ_Z :=
  28948022309329048855892746252171976963363056481941647379679742748393362948097.

Definition ActionGardenZ_zZero : ActionGardenZ_Z := Z.of_nat 0.
Definition ActionGardenZ_zOne : ActionGardenZ_Z := Z.of_nat 1.
Definition ActionGardenZ_zTwo : ActionGardenZ_Z := Z.of_nat 2.

Definition ActionGardenZ_zAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z := Z.add left right.
Definition ActionGardenZ_zSub (left right : ActionGardenZ_Z) : ActionGardenZ_Z := Z.sub left right.
Definition ActionGardenZ_zMul (left right : ActionGardenZ_Z) : ActionGardenZ_Z := Z.mul left right.
Definition ActionGardenZ_zNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z := Z.opp value.
Definition ActionGardenZ_zDiv (dividend divisor : ActionGardenZ_Z) : ActionGardenZ_Z := Z.div dividend divisor.
Definition ActionGardenZ_zMod (dividend modulus : ActionGardenZ_Z) : ActionGardenZ_Z := Z.modulo dividend modulus.
Definition ActionGardenZ_zPowNat (base : ActionGardenZ_Z) (exponent : nat) : ActionGardenZ_Z :=
  Z.pow base (Z.of_nat exponent).
Definition ActionGardenZ_zEq (left right : ActionGardenZ_Z) : bool := Z.eqb left right.

Definition ActionGardenZ_inRange (value upperBound : ActionGardenZ_Z) : Prop :=
  Z.le ActionGardenZ_zZero value /\ Z.lt value upperBound.

Definition ActionGardenZ_normalize (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_zMod value modulus.

Definition ActionGardenZ_addModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize modulus (ActionGardenZ_zAdd left right).

Definition ActionGardenZ_subModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize modulus (ActionGardenZ_zSub left right).

Definition ActionGardenZ_mulModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize modulus (ActionGardenZ_zMul left right).

Definition ActionGardenZ_negModulo (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize modulus (ActionGardenZ_zNeg value).

Definition ActionGardenZ_baseNormalize (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize ActionGardenZ_pallasBaseModulus value.

Definition ActionGardenZ_baseAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_addModulo ActionGardenZ_pallasBaseModulus left right.

Definition ActionGardenZ_baseSub (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_subModulo ActionGardenZ_pallasBaseModulus left right.

Definition ActionGardenZ_baseMul (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_mulModulo ActionGardenZ_pallasBaseModulus left right.

Definition ActionGardenZ_baseNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_negModulo ActionGardenZ_pallasBaseModulus value.

Definition ActionGardenZ_baseEqual (left right : ActionGardenZ_Z) : bool :=
  ActionGardenZ_zEq (ActionGardenZ_baseNormalize left) (ActionGardenZ_baseNormalize right).

Definition ActionGardenZ_baseCanonical (value : ActionGardenZ_Z) : Prop :=
  ActionGardenZ_baseNormalize value = value.

Definition ActionGardenZ_scalarNormalize (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_normalize ActionGardenZ_pallasScalarModulus value.

Definition ActionGardenZ_scalarAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_addModulo ActionGardenZ_pallasScalarModulus left right.

Definition ActionGardenZ_scalarNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_negModulo ActionGardenZ_pallasScalarModulus value.

Definition ActionGardenZ_scalarCanonical (value : ActionGardenZ_Z) : Prop :=
  ActionGardenZ_scalarNormalize value = value.

Definition ActionGardenZ_baseToScalar (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_scalarNormalize (ActionGardenZ_baseNormalize value).

Definition ActionGardenZ_modInverse (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  let reduced := ActionGardenZ_normalize modulus value in
  if ActionGardenZ_zEq reduced ActionGardenZ_zZero then ActionGardenZ_zZero
  else ActionGardenZ_normalize modulus
    (ActionGardenZ_zPowNat reduced (Z.to_nat (ActionGardenZ_zSub modulus ActionGardenZ_zTwo))).

Definition ActionGardenZ_baseInverse (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_modInverse ActionGardenZ_pallasBaseModulus value.

Definition ActionGardenZ_baseDiv (numerator denominator : ActionGardenZ_Z) : ActionGardenZ_Z :=
  ActionGardenZ_baseMul numerator (ActionGardenZ_baseInverse denominator).

(** ** Affine Pallas points

    Points are explicit pairs of canonical base-field integers.  [(0, 0)] is
    the identity sentinel used by both circuit developments.  [ActionGardenZ_pointAdd] is
    total, but the Action validity predicate records the on-curve and
    Sinsemilla non-degeneracy conditions under which it has the protocol
    interpretation. *)

Definition ActionGardenZ_Point : Type := ActionGardenPointData.

Definition ActionGardenZ_pointIdentity : ActionGardenZ_Point :=
  {| actionGardenPointX := ActionGardenZ_zZero; actionGardenPointY := ActionGardenZ_zZero |}.

Definition ActionGardenZ_pointNormalize (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  {| actionGardenPointX := ActionGardenZ_baseNormalize point.(actionGardenPointX); actionGardenPointY := ActionGardenZ_baseNormalize point.(actionGardenPointY) |}.

Definition ActionGardenZ_pointIsIdentity (point : ActionGardenZ_Point) : bool :=
  andb (ActionGardenZ_baseEqual point.(actionGardenPointX) ActionGardenZ_zZero) (ActionGardenZ_baseEqual point.(actionGardenPointY) ActionGardenZ_zZero).

Definition ActionGardenZ_pointCanonical (point : ActionGardenZ_Point) : Prop :=
  ActionGardenZ_baseCanonical point.(actionGardenPointX) /\ ActionGardenZ_baseCanonical point.(actionGardenPointY).

Definition ActionGardenZ_pointOnCurve (point : ActionGardenZ_Point) : Prop :=
  let xSquared := ActionGardenZ_baseMul point.(actionGardenPointX) point.(actionGardenPointX) in
  let xCubed := ActionGardenZ_baseMul xSquared point.(actionGardenPointX) in
  let right := ActionGardenZ_baseAdd xCubed (Z.of_nat 5) in
  ActionGardenZ_baseMul point.(actionGardenPointY) point.(actionGardenPointY) = right.

Definition ActionGardenZ_pointValid (point : ActionGardenZ_Point) : Prop :=
  ActionGardenZ_pointNormalize point = ActionGardenZ_pointIdentity \/ ActionGardenZ_pointOnCurve point.

Definition ActionGardenZ_pointNeg (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  if ActionGardenZ_pointIsIdentity point then ActionGardenZ_pointIdentity
  else {| actionGardenPointX := ActionGardenZ_baseNormalize point.(actionGardenPointX); actionGardenPointY := ActionGardenZ_baseNeg point.(actionGardenPointY) |}.

Definition ActionGardenZ_pointAdd (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  if ActionGardenZ_pointIsIdentity left then ActionGardenZ_pointNormalize right
  else if ActionGardenZ_pointIsIdentity right then ActionGardenZ_pointNormalize left
  else if ActionGardenZ_baseEqual left.(actionGardenPointX) right.(actionGardenPointX) then
    if ActionGardenZ_baseEqual (ActionGardenZ_baseAdd left.(actionGardenPointY) right.(actionGardenPointY)) ActionGardenZ_zZero then ActionGardenZ_pointIdentity
    else
      let numerator :=
        ActionGardenZ_baseAdd
          (ActionGardenZ_baseMul (Z.of_nat 3) (ActionGardenZ_baseMul left.(actionGardenPointX) left.(actionGardenPointX)))
          ActionGardenZ_zZero in
      let denominator := ActionGardenZ_baseMul ActionGardenZ_zTwo left.(actionGardenPointY) in
      let slope := ActionGardenZ_baseDiv numerator denominator in
      let resultX :=
        ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) left.(actionGardenPointX)) right.(actionGardenPointX) in
      let resultY :=
        ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub left.(actionGardenPointX) resultX)) left.(actionGardenPointY) in
      {| actionGardenPointX := resultX; actionGardenPointY := resultY |}
  else
    let numerator := ActionGardenZ_baseSub right.(actionGardenPointY) left.(actionGardenPointY) in
    let denominator := ActionGardenZ_baseSub right.(actionGardenPointX) left.(actionGardenPointX) in
    let slope := ActionGardenZ_baseDiv numerator denominator in
    let resultX :=
      ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) left.(actionGardenPointX)) right.(actionGardenPointX) in
    let resultY :=
      ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub left.(actionGardenPointX) resultX)) left.(actionGardenPointY) in
    {| actionGardenPointX := resultX; actionGardenPointY := resultY |}.

Fixpoint ActionGardenZ_pointNatMul (scalar : nat) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  match scalar with
  | O => ActionGardenZ_pointIdentity
  | S remaining => ActionGardenZ_pointAdd (ActionGardenZ_pointNatMul remaining point) point
  end.

Definition ActionGardenZ_scalarMul (scalar : ActionGardenZ_Z) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  ActionGardenZ_pointNatMul (Z.to_nat (ActionGardenZ_scalarNormalize scalar)) point.

Definition ActionGardenZ_basePointMul (baseValue : ActionGardenZ_Z) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  ActionGardenZ_pointNatMul (Z.to_nat (ActionGardenZ_baseNormalize baseValue)) point.

Definition ActionGardenZ_extractX (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  if ActionGardenZ_pointIsIdentity point then ActionGardenZ_zZero else ActionGardenZ_baseNormalize point.(actionGardenPointX).

(** ** Poseidon P128Pow5T3

    The constants are data in [ActionGardenZ_PoseidonParameters].  The schedule is four full
    rounds, twenty-eight pairs of partial rounds, and four final full rounds,
    matching the 64-round Orchard coreNullifier permutation. *)

Definition ActionGardenZ_State3 : Type := ActionGardenState3Data.

Record ActionGardenZ_Matrix3 : Type := {
  ActionGardenZ_m00 : ActionGardenZ_Z;
  ActionGardenZ_m01 : ActionGardenZ_Z;
  ActionGardenZ_m02 : ActionGardenZ_Z;
  ActionGardenZ_m10 : ActionGardenZ_Z;
  ActionGardenZ_m11 : ActionGardenZ_Z;
  ActionGardenZ_m12 : ActionGardenZ_Z;
  ActionGardenZ_m20 : ActionGardenZ_Z;
  ActionGardenZ_m21 : ActionGardenZ_Z;
  ActionGardenZ_m22 : ActionGardenZ_Z;
}.

Record ActionGardenZ_PoseidonParameters : Type := {
  ActionGardenZ_roundConstant : ActionGardenZ_Z -> ActionGardenZ_State3;
  ActionGardenZ_mds : ActionGardenZ_Matrix3;
}.

Definition ActionGardenZ_basePow5 (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  let square := ActionGardenZ_baseMul value value in
  ActionGardenZ_baseMul (ActionGardenZ_baseMul square square) value.

Definition ActionGardenZ_matrixApply (matrix : ActionGardenZ_Matrix3) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  {|
    ActionGardenZ_x0 :=
      ActionGardenZ_baseAdd
        (ActionGardenZ_baseAdd
          (ActionGardenZ_baseMul state.(ActionGardenZ_x0) matrix.(ActionGardenZ_m00))
          (ActionGardenZ_baseMul state.(ActionGardenZ_x1) matrix.(ActionGardenZ_m01)))
        (ActionGardenZ_baseMul state.(ActionGardenZ_x2) matrix.(ActionGardenZ_m02));
    ActionGardenZ_x1 :=
      ActionGardenZ_baseAdd
        (ActionGardenZ_baseAdd
          (ActionGardenZ_baseMul state.(ActionGardenZ_x0) matrix.(ActionGardenZ_m10))
          (ActionGardenZ_baseMul state.(ActionGardenZ_x1) matrix.(ActionGardenZ_m11)))
        (ActionGardenZ_baseMul state.(ActionGardenZ_x2) matrix.(ActionGardenZ_m12));
    ActionGardenZ_x2 :=
      ActionGardenZ_baseAdd
        (ActionGardenZ_baseAdd
          (ActionGardenZ_baseMul state.(ActionGardenZ_x0) matrix.(ActionGardenZ_m20))
          (ActionGardenZ_baseMul state.(ActionGardenZ_x1) matrix.(ActionGardenZ_m21)))
        (ActionGardenZ_baseMul state.(ActionGardenZ_x2) matrix.(ActionGardenZ_m22))
  |}.

Definition ActionGardenZ_poseidonFullRound
    (parameters : ActionGardenZ_PoseidonParameters) (round : ActionGardenZ_Z) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  let constants := parameters.(ActionGardenZ_roundConstant) round in
  ActionGardenZ_matrixApply parameters.(ActionGardenZ_mds) {|
    ActionGardenZ_x0 := ActionGardenZ_basePow5 (ActionGardenZ_baseAdd state.(ActionGardenZ_x0) constants.(ActionGardenZ_x0));
    ActionGardenZ_x1 := ActionGardenZ_basePow5 (ActionGardenZ_baseAdd state.(ActionGardenZ_x1) constants.(ActionGardenZ_x1));
    ActionGardenZ_x2 := ActionGardenZ_basePow5 (ActionGardenZ_baseAdd state.(ActionGardenZ_x2) constants.(ActionGardenZ_x2))
  |}.

Definition ActionGardenZ_poseidonPartialPair
    (parameters : ActionGardenZ_PoseidonParameters) (round : ActionGardenZ_Z) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  let firstConstants := parameters.(ActionGardenZ_roundConstant) round in
  let firstMixed := ActionGardenZ_matrixApply parameters.(ActionGardenZ_mds) {|
    ActionGardenZ_x0 := ActionGardenZ_basePow5 (ActionGardenZ_baseAdd state.(ActionGardenZ_x0) firstConstants.(ActionGardenZ_x0));
    ActionGardenZ_x1 := ActionGardenZ_baseAdd state.(ActionGardenZ_x1) firstConstants.(ActionGardenZ_x1);
    ActionGardenZ_x2 := ActionGardenZ_baseAdd state.(ActionGardenZ_x2) firstConstants.(ActionGardenZ_x2)
  |} in
  let secondConstants := parameters.(ActionGardenZ_roundConstant) (ActionGardenZ_zAdd round ActionGardenZ_zOne) in
  ActionGardenZ_matrixApply parameters.(ActionGardenZ_mds) {|
    ActionGardenZ_x0 := ActionGardenZ_basePow5 (ActionGardenZ_baseAdd firstMixed.(ActionGardenZ_x0) secondConstants.(ActionGardenZ_x0));
    ActionGardenZ_x1 := ActionGardenZ_baseAdd firstMixed.(ActionGardenZ_x1) secondConstants.(ActionGardenZ_x1);
    ActionGardenZ_x2 := ActionGardenZ_baseAdd firstMixed.(ActionGardenZ_x2) secondConstants.(ActionGardenZ_x2)
  |}.

Fixpoint ActionGardenZ_iterateIndexedFrom {A : Type}
    (count index : nat) (step : nat -> A -> A) (initial : A) : A :=
  match count with
  | O => initial
  | S remaining =>
      ActionGardenZ_iterateIndexedFrom remaining (S index) step (step index initial)
  end.

Definition ActionGardenZ_iterateIndexed {A : Type}
    (count : nat) (step : nat -> A -> A) (initial : A) : A :=
  ActionGardenZ_iterateIndexedFrom count O step initial.

Definition ActionGardenZ_poseidonPermute
    (parameters : ActionGardenZ_PoseidonParameters) (initial : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  let afterFirstFull :=
    ActionGardenZ_iterateIndexed 4%nat
      (fun index state =>
        ActionGardenZ_poseidonFullRound parameters (Z.of_nat index) state)
      initial in
  let afterPartial :=
    ActionGardenZ_iterateIndexed 28%nat
      (fun index state =>
        ActionGardenZ_poseidonPartialPair parameters
          (Z.of_nat (Nat.add 4%nat (Nat.mul 2%nat index))) state)
      afterFirstFull in
  ActionGardenZ_iterateIndexed 4%nat
    (fun index state =>
      ActionGardenZ_poseidonFullRound parameters
        (Z.of_nat (Nat.add 60%nat index)) state)
    afterPartial.

Definition ActionGardenZ_poseidonHash2
    (parameters : ActionGardenZ_PoseidonParameters) (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  let capacity :=
    ActionGardenZ_baseNormalize (ActionGardenZ_zMul (Z.of_nat 2) (ActionGardenZ_zPowNat (Z.of_nat 2) 64%nat)) in
  (** Garden's constant-length-two sponge enters the permutation with the two
      message words already in the state.  This direct form corresponds as a
      total function for arbitrary [ActionGardenZ_Z] inputs. *)
  (ActionGardenZ_poseidonPermute parameters {|
    ActionGardenZ_x0 := left;
    ActionGardenZ_x1 := right;
    ActionGardenZ_x2 := capacity
  |}).(ActionGardenZ_x0).

(** ** Concrete deployed Orchard parameters *)

Definition ActionGardenZ_listGetDAtZ {A : Type}
    (values : PrimArray.array A) (index : ActionGardenZ_Z) (fallback : A) : A :=
  let normalizedIndex := Z.max ActionGardenZ_zZero index in
  if Z.ltb normalizedIndex
      (Uint63.to_Z (PrimArray.length values))
  then PrimArray.get values (Uint63.of_Z normalizedIndex)
  else fallback.

Definition ActionGardenZ_orchardPoseidonRoundConstants : PrimArray.array ActionGardenZ_State3 :=
  actionGardenPoseidonRoundConstantsData.

Definition ActionGardenZ_orchardPoseidonRoundConstant (round : ActionGardenZ_Z) : ActionGardenZ_State3 :=
  ActionGardenZ_listGetDAtZ ActionGardenZ_orchardPoseidonRoundConstants round
    {| ActionGardenZ_x0 := ActionGardenZ_zZero; ActionGardenZ_x1 := ActionGardenZ_zZero; ActionGardenZ_x2 := ActionGardenZ_zZero |}.

Definition ActionGardenZ_orchardPoseidonMds : ActionGardenZ_Matrix3 := {|
  ActionGardenZ_m00 := 4844513277385895547578596669280046666372576567380472439333234012806535256931;
  ActionGardenZ_m01 := 22420227485671588580194914215361958133919537309433003325602272145024023440222;
  ActionGardenZ_m02 := 3505906565384614297249013623188452104971681200991017471148427242055139865693;
  ActionGardenZ_m10 := 15918204248318370126242808206081613758525089148509539575126649371340283647612;
  ActionGardenZ_m11 := 17094040714843518372934853765548613673798971581804674915582475057795168500270;
  ActionGardenZ_m12 := 15812769689003694604229247543370933348074043003262912834067271177893884949626;
  ActionGardenZ_m20 := 20880359470746774736726481852287259022559450533689220298394450009637377072100;
  ActionGardenZ_m21 := 13164192954509875252051728398669721690665762613581286296450591265062029506148;
  ActionGardenZ_m22 := 27123552791154096240274588421608257979835967097480491934880175221940903501553
|}.

Definition ActionGardenZ_orchardPoseidonParameters : ActionGardenZ_PoseidonParameters := {|
  ActionGardenZ_roundConstant := ActionGardenZ_orchardPoseidonRoundConstant;
  ActionGardenZ_mds := ActionGardenZ_orchardPoseidonMds
|}.

Definition ActionGardenZ_orchardSinsemillaGenerators : PrimArray.array ActionGardenZ_Point :=
  actionGardenSinsemillaGeneratorsData.

Definition ActionGardenZ_orchardSinsemillaGenerator (chunk : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_listGetDAtZ ActionGardenZ_orchardSinsemillaGenerators chunk ActionGardenZ_pointIdentity.

Definition ActionGardenZ_orchardNoteCommitQ : ActionGardenZ_Point := {|
  actionGardenPointX := 10629404576683096409262958701336170057000067777256141967953463442979689100381;
  actionGardenPointY := 22898949290933268079297281211505753011910178734473470279111609228438645877859
|}.

Definition ActionGardenZ_orchardCommitIvkQ : ActionGardenZ_Point := {|
  actionGardenPointX := 2593820817260930114322133467408868473290945477826616247349533151445648376562;
  actionGardenPointY := 12214744946019415453501880094709511126888074367290315326445800415816181472958
|}.

Definition ActionGardenZ_orchardMerkleCrhQ : ActionGardenZ_Point := {|
  actionGardenPointX := 9991206725476878888751475603038274618448000607209514551456795194094072219296;
  actionGardenPointY := 24209798415301550423396126020228723009317736024280831393239261884225294625378
|}.

Definition ActionGardenZ_orchardSpendAuthG : ActionGardenZ_Point := {|
  actionGardenPointX := 25027635063850382358429654596649554085117301901282348152423547104939793041763;
  actionGardenPointY := 12128007492603938773365931378340937928001494939630793217712875072231079427017
|}.

Definition ActionGardenZ_orchardValueCommitVG : ActionGardenZ_Point := {|
  actionGardenPointX := 21457208314186520936880902219424053485005045883401337627148481900742711001959;
  actionGardenPointY := 20379375922573002911833717643813254676246486412159279022689151936901102105230
|}.

Definition ActionGardenZ_orchardValueCommitRG : ActionGardenZ_Point := {|
  actionGardenPointX := 3597772235883004661259329170144280297379687592370687591147658848249887611537;
  actionGardenPointY := 16317546749781193797530044795837656238506071957562073482938086095508632426954
|}.

Definition ActionGardenZ_orchardNullifierKG : ActionGardenZ_Point := {|
  actionGardenPointX := 17144890976040313974462754624161095328261290075490099718273142830262355741301;
  actionGardenPointY := 9661337292872073193100428608853316471968232023361741282759000480983323509196
|}.

Definition ActionGardenZ_orchardNoteCommitRG : ActionGardenZ_Point := {|
  actionGardenPointX := 17502433695644481444785977856966854265310331039772160001849803703443502427667;
  actionGardenPointY := 27531606546556235994383748883097777001194017792923801570415255878186539366371
|}.

Definition ActionGardenZ_orchardCommitIvkRG : ActionGardenZ_Point := {|
  actionGardenPointX := 17022113834174368664964072539940476916905682548990455171271428285673934201112;
  actionGardenPointY := 18912017636736613471143674001158885358143653198146604093009134371854861983145
|}.

(** The public Garden layer below refers to the deployed tables through these
    named accessors.  Keeping the storage boundary opaque prevents Rocq's
    library cooker from recursively inlining all 1,088 rows into every helper;
    these remain definitions and proof files may locally mark them
    [Transparent] when auditing concrete entries. *)
Strategy opaque
  [ActionGardenZ_orchardPoseidonRoundConstants
   ActionGardenZ_orchardPoseidonRoundConstant
   ActionGardenZ_orchardPoseidonMds
   ActionGardenZ_orchardPoseidonParameters
   ActionGardenZ_orchardSinsemillaGenerators
   ActionGardenZ_orchardSinsemillaGenerator].

(** ** Garden-shaped Action specification *)

Record ActionGardenZ_Params : Type := {
  ActionGardenZ_paramsNoteCommitQ : ActionGardenZ_Point;
  ActionGardenZ_paramsCommitIvkQ : ActionGardenZ_Point;
  ActionGardenZ_paramsMerkleCrhQ : ActionGardenZ_Point;
}.

Definition ActionGardenZ_orchardParams : ActionGardenZ_Params := {|
  ActionGardenZ_paramsNoteCommitQ := ActionGardenZ_orchardNoteCommitQ;
  ActionGardenZ_paramsCommitIvkQ := ActionGardenZ_orchardCommitIvkQ;
  ActionGardenZ_paramsMerkleCrhQ := ActionGardenZ_orchardMerkleCrhQ
|}.

Definition ActionGardenZ_pointAddGarden (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  if ActionGardenZ_zEq left.(actionGardenPointX) ActionGardenZ_zZero then right
  else if ActionGardenZ_zEq right.(actionGardenPointX) ActionGardenZ_zZero then left
  else if andb (ActionGardenZ_zEq left.(actionGardenPointX) right.(actionGardenPointX))
      (ActionGardenZ_zEq (ActionGardenZ_baseAdd left.(actionGardenPointY) right.(actionGardenPointY)) ActionGardenZ_zZero)
  then ActionGardenZ_pointIdentity
  else
    let slope :=
      if ActionGardenZ_zEq left.(actionGardenPointX) right.(actionGardenPointX)
      then
        ActionGardenZ_baseDiv
          (ActionGardenZ_baseMul (Z.of_nat 3) (ActionGardenZ_baseMul left.(actionGardenPointX) left.(actionGardenPointX)))
          (ActionGardenZ_baseMul ActionGardenZ_zTwo left.(actionGardenPointY))
      else
        ActionGardenZ_baseDiv
          (ActionGardenZ_baseSub right.(actionGardenPointY) left.(actionGardenPointY))
          (ActionGardenZ_baseSub right.(actionGardenPointX) left.(actionGardenPointX)) in
    let resultX :=
      ActionGardenZ_baseSub
        (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) left.(actionGardenPointX))
        right.(actionGardenPointX) in
    {|
      actionGardenPointX := resultX;
      actionGardenPointY := ActionGardenZ_baseSub
        (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub left.(actionGardenPointX) resultX))
        left.(actionGardenPointY)
    |}.

Definition ActionGardenZ_extractXGarden (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  point.(actionGardenPointX).

Definition ActionGardenZ_pointAddIncomplete (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  let slope :=
    ActionGardenZ_baseDiv
      (ActionGardenZ_baseSub left.(actionGardenPointY) right.(actionGardenPointY))
      (ActionGardenZ_baseSub left.(actionGardenPointX) right.(actionGardenPointX)) in
  let resultX :=
    ActionGardenZ_baseSub
      (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) left.(actionGardenPointX))
      right.(actionGardenPointX) in
  {|
    actionGardenPointX := resultX;
    actionGardenPointY :=
      ActionGardenZ_baseSub
        (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub left.(actionGardenPointX) resultX))
        left.(actionGardenPointY)
  |}.

Definition ActionGardenZ_sinsemillaRound (accumulator : ActionGardenZ_Point) (word : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_pointAddIncomplete
    (ActionGardenZ_pointAddIncomplete accumulator (ActionGardenZ_orchardSinsemillaGenerator word))
    accumulator.

Definition ActionGardenZ_sinsemillaHashToPointGarden
    (domain : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : ActionGardenZ_Point :=
  fold_left ActionGardenZ_sinsemillaRound words domain.

Definition ActionGardenZ_pointIdentityGarden (point : ActionGardenZ_Point) : Prop :=
  point.(actionGardenPointX) = ActionGardenZ_zZero /\ point.(actionGardenPointY) = ActionGardenZ_zZero.

Definition ActionGardenZ_sinsemillaRoundDefined
    (accumulator : ActionGardenZ_Point) (word : ActionGardenZ_Z) : Prop :=
  let generator := ActionGardenZ_orchardSinsemillaGenerator word in
  let firstSum := ActionGardenZ_pointAddIncomplete accumulator generator in
  ~ ActionGardenZ_pointIdentityGarden accumulator /\
  ~ ActionGardenZ_pointIdentityGarden generator /\
  ActionGardenZ_baseNormalize accumulator.(actionGardenPointX) <> ActionGardenZ_baseNormalize generator.(actionGardenPointX) /\
  ~ ActionGardenZ_pointIdentityGarden firstSum /\
  ActionGardenZ_baseNormalize firstSum.(actionGardenPointX) <> ActionGardenZ_baseNormalize accumulator.(actionGardenPointX).

Fixpoint ActionGardenZ_sinsemillaHashDefinedFromGarden
    (accumulator : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : Prop :=
  match words with
  | nil => True
  | cons word rest =>
      ActionGardenZ_sinsemillaRoundDefined accumulator word /\
      ActionGardenZ_sinsemillaHashDefinedFromGarden
        (ActionGardenZ_sinsemillaRound accumulator word) rest
  end.

Definition ActionGardenZ_sinsemillaHashDefinedGarden
    (domain : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : Prop :=
  ActionGardenZ_sinsemillaHashDefinedFromGarden domain words.

Fixpoint ActionGardenZ_wordsLe (count : nat) (value : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  match count with
  | O => nil
  | S remaining =>
      cons
        (ActionGardenZ_zMod value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat))
        (ActionGardenZ_wordsLe remaining (ActionGardenZ_zDiv value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat)))
  end.

Definition ActionGardenZ_pointParity (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  ActionGardenZ_zMod point.(actionGardenPointY) ActionGardenZ_zTwo.

Definition ActionGardenZ_noteCommitMessageGarden
    (gd pkd : ActionGardenZ_Point) (value rho psi : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  ActionGardenZ_wordsLe 109%nat
    (ActionGardenZ_zAdd
      (ActionGardenZ_zAdd
        (ActionGardenZ_zAdd
          (ActionGardenZ_zAdd
            (ActionGardenZ_zAdd
              (ActionGardenZ_zAdd
                (ActionGardenZ_zAdd
                  (ActionGardenZ_zAdd
                    (ActionGardenZ_extractXGarden gd)
                    (ActionGardenZ_zMul (ActionGardenZ_pointParity gd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat)))
                  (ActionGardenZ_zMul (ActionGardenZ_extractXGarden pkd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 256%nat)))
                (ActionGardenZ_zMul (ActionGardenZ_pointParity pkd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 511%nat)))
              (ActionGardenZ_zMul value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 512%nat)))
            (ActionGardenZ_zMul rho (ActionGardenZ_zPowNat ActionGardenZ_zTwo 576%nat)))
          (ActionGardenZ_zMul psi (ActionGardenZ_zPowNat ActionGardenZ_zTwo 831%nat)))
        ActionGardenZ_zZero)
      ActionGardenZ_zZero).

Definition ActionGardenZ_commitIvkMessageGarden (ak nk : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  ActionGardenZ_wordsLe 51%nat (ActionGardenZ_zAdd ak (ActionGardenZ_zMul nk (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat))).

Definition ActionGardenZ_merkleMessageGarden (layer left right : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  ActionGardenZ_wordsLe 52%nat
    (ActionGardenZ_zAdd layer
      (ActionGardenZ_zAdd
        (ActionGardenZ_zMul left (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat))
        (ActionGardenZ_zMul right (ActionGardenZ_zPowNat ActionGardenZ_zTwo 265%nat)))).

Definition ActionGardenZ_merkleLayer
    (domain : ActionGardenZ_Point) (layer node sibling : ActionGardenZ_Z) (isRight : bool) : ActionGardenZ_Z :=
  let left := if isRight then sibling else node in
  let right := if isRight then node else sibling in
  ActionGardenZ_extractXGarden
    (ActionGardenZ_sinsemillaHashToPointGarden domain
      (ActionGardenZ_merkleMessageGarden layer left right)).

Definition ActionGardenZ_merkleRootGarden
    (domain : ActionGardenZ_Point) (leaf : ActionGardenZ_Z) (path : list (ActionGardenZ_Z * ActionGardenZ_Z * bool)) : ActionGardenZ_Z :=
  fold_left
    (fun node element =>
      ActionGardenZ_merkleLayer domain (fst (fst element)) node
        (snd (fst element)) (snd element))
    path leaf.

Definition ActionGardenZ_merkleStepDefinedGarden
    (domain : ActionGardenZ_Point) (node layer sibling : ActionGardenZ_Z) (isRight : bool) : Prop :=
  let left := if isRight then sibling else node in
  let right := if isRight then node else sibling in
  ActionGardenZ_sinsemillaHashDefinedGarden domain
    (ActionGardenZ_merkleMessageGarden layer left right).

Inductive ActionGardenZ_merklePathDefinedFromGarden
    (domain : ActionGardenZ_Point) : ActionGardenZ_Z -> list (ActionGardenZ_Z * ActionGardenZ_Z * bool) -> Prop :=
  | ActionGardenMerklePathDefinedNil (node : ActionGardenZ_Z) :
      ActionGardenZ_merklePathDefinedFromGarden domain node nil
  | ActionGardenMerklePathDefinedCons
      (node nextNode layer sibling : ActionGardenZ_Z) (isRight : bool)
      (rest : list (ActionGardenZ_Z * ActionGardenZ_Z * bool)) :
      ActionGardenZ_merkleStepDefinedGarden domain node layer sibling isRight ->
      nextNode = ActionGardenZ_merkleLayer domain layer node sibling isRight ->
      ActionGardenZ_merklePathDefinedFromGarden domain nextNode rest ->
      ActionGardenZ_merklePathDefinedFromGarden domain node
        (cons ((layer, sibling), isRight) rest).

Definition ActionGardenZ_merklePathDefinedGarden
    (domain : ActionGardenZ_Point) (leaf : ActionGardenZ_Z)
    (path : list (ActionGardenZ_Z * ActionGardenZ_Z * bool)) : Prop :=
  ActionGardenZ_merklePathDefinedFromGarden domain leaf path.

Fixpoint ActionGardenZ_pathLayersFrom
    (expected : ActionGardenZ_Z) (path : list (ActionGardenZ_Z * ActionGardenZ_Z * bool)) : Prop :=
  match path with
  | nil => True
  | cons element rest =>
      fst (fst element) = expected /\
      ActionGardenZ_pathLayersFrom (ActionGardenZ_zAdd expected ActionGardenZ_zOne) rest
  end.

Definition ActionGardenZ_pathLayersCanonical
    (path : list (ActionGardenZ_Z * ActionGardenZ_Z * bool)) : Prop :=
  ActionGardenZ_pathLayersFrom ActionGardenZ_zZero path.

Record ActionGardenZ_ActionInputs : Type := {
  ActionGardenZ_inAk : ActionGardenZ_Point;
  ActionGardenZ_inNk : ActionGardenZ_Z;
  ActionGardenZ_inRhoOld : ActionGardenZ_Z;
  ActionGardenZ_inPsiOld : ActionGardenZ_Z;
  ActionGardenZ_inCmOld : ActionGardenZ_Point;
  ActionGardenZ_inGdOld : ActionGardenZ_Point;
  ActionGardenZ_inPkdOld : ActionGardenZ_Point;
  ActionGardenZ_inVOld : ActionGardenZ_Z;
  ActionGardenZ_inRivk : ActionGardenZ_Z;
  ActionGardenZ_inAlpha : ActionGardenZ_Z;
  ActionGardenZ_inAnchorPublic : ActionGardenZ_Z;
  ActionGardenZ_inRcv : ActionGardenZ_Z;
  ActionGardenZ_inMagnitude : ActionGardenZ_Z;
  ActionGardenZ_inSign : ActionGardenZ_Z;
  ActionGardenZ_inLeaf : ActionGardenZ_Z;
  ActionGardenZ_inPath : list (ActionGardenZ_Z * ActionGardenZ_Z * bool);
  ActionGardenZ_inGdNew : ActionGardenZ_Point;
  ActionGardenZ_inPkdNew : ActionGardenZ_Point;
  ActionGardenZ_inVNew : ActionGardenZ_Z;
  ActionGardenZ_inPsiNew : ActionGardenZ_Z;
  ActionGardenZ_inRcmNew : ActionGardenZ_Z;
}.

Record ActionGardenZ_FullActionInputs : Type := {
  ActionGardenZ_fullAction : ActionGardenZ_ActionInputs;
  ActionGardenZ_fullRcmOld : ActionGardenZ_Z;
  ActionGardenZ_fullEnableSpend : ActionGardenZ_Z;
  ActionGardenZ_fullEnableOutput : ActionGardenZ_Z;
  ActionGardenZ_fullDisableCrossAddress : ActionGardenZ_Z;
}.

Record ActionGardenZ_ActionOutputs : Type := {
  ActionGardenZ_outAnchor : ActionGardenZ_Z;
  ActionGardenZ_outCvNet : ActionGardenZ_Point;
  ActionGardenZ_outNfOld : ActionGardenZ_Z;
  ActionGardenZ_outRk : ActionGardenZ_Point;
  ActionGardenZ_outCmx : ActionGardenZ_Z;
}.

Definition ActionGardenZ_signedNetValue (magnitude sign : ActionGardenZ_Z) : ActionGardenZ_Z :=
  if ActionGardenZ_zEq sign ActionGardenZ_zOne then magnitude else ActionGardenZ_zNeg magnitude.

Definition ActionGardenZ_spendAuthRandomize (ak : ActionGardenZ_Point) (alpha : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_pointAddGarden ak (ActionGardenZ_scalarMul alpha ActionGardenZ_orchardSpendAuthG).

Definition ActionGardenZ_valueCommit (value randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_pointAddGarden
    (ActionGardenZ_scalarMul value ActionGardenZ_orchardValueCommitVG)
    (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardValueCommitRG).

Definition ActionGardenZ_nullifier (nk rho psi : ActionGardenZ_Z) (cm : ActionGardenZ_Point) : ActionGardenZ_Z :=
  let hash := ActionGardenZ_poseidonHash2 ActionGardenZ_orchardPoseidonParameters nk rho in
  let scalar := ActionGardenZ_baseAdd hash psi in
  ActionGardenZ_extractXGarden
    (ActionGardenZ_pointAddGarden
      (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardNullifierKG)
      cm).

Definition ActionGardenZ_noteCommit
    (parameters : ActionGardenZ_Params)
    (gd pkd : ActionGardenZ_Point) (value rho psi randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_pointAddGarden
    (ActionGardenZ_sinsemillaHashToPointGarden parameters.(ActionGardenZ_paramsNoteCommitQ)
      (ActionGardenZ_noteCommitMessageGarden gd pkd value rho psi))
    (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardNoteCommitRG).

Definition ActionGardenZ_commitIvk
    (parameters : ActionGardenZ_Params) (ak nk randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  ActionGardenZ_pointAddGarden
    (ActionGardenZ_sinsemillaHashToPointGarden parameters.(ActionGardenZ_paramsCommitIvkQ)
      (ActionGardenZ_commitIvkMessageGarden ak nk))
    (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardCommitIvkRG).

Definition ActionGardenZ_actionParametersValid (parameters : ActionGardenZ_Params) : Prop :=
  ActionGardenZ_pointCanonical parameters.(ActionGardenZ_paramsNoteCommitQ) /\
  ActionGardenZ_pointCanonical parameters.(ActionGardenZ_paramsCommitIvkQ) /\
  ActionGardenZ_pointCanonical parameters.(ActionGardenZ_paramsMerkleCrhQ) /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardSpendAuthG /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardValueCommitVG /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardValueCommitRG /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardNullifierKG /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardNoteCommitRG /\
  ActionGardenZ_pointCanonical ActionGardenZ_orchardCommitIvkRG /\
  ActionGardenZ_pointOnCurve parameters.(ActionGardenZ_paramsNoteCommitQ) /\
  ActionGardenZ_pointOnCurve parameters.(ActionGardenZ_paramsCommitIvkQ) /\
  ActionGardenZ_pointOnCurve parameters.(ActionGardenZ_paramsMerkleCrhQ) /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardSpendAuthG /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardValueCommitVG /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardValueCommitRG /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardNullifierKG /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardNoteCommitRG /\
  ActionGardenZ_pointOnCurve ActionGardenZ_orchardCommitIvkRG /\
  forall word : ActionGardenZ_Z,
    ActionGardenZ_inRange word (Z.of_nat 1024) ->
    ActionGardenZ_pointCanonical (ActionGardenZ_orchardSinsemillaGenerator word) /\
    ActionGardenZ_pointOnCurve (ActionGardenZ_orchardSinsemillaGenerator word).

Definition ActionGardenZ_actionPointsTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inAk) /\
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inCmOld) /\
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inGdOld) /\
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inPkdOld) /\
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inGdNew) /\
  ActionGardenZ_pointCanonical core.(ActionGardenZ_inPkdNew) /\
  ActionGardenZ_pointOnCurve core.(ActionGardenZ_inAk) /\
  ActionGardenZ_pointValid core.(ActionGardenZ_inCmOld) /\
  ActionGardenZ_pointOnCurve core.(ActionGardenZ_inGdOld) /\
  ActionGardenZ_pointOnCurve core.(ActionGardenZ_inPkdOld) /\
  ActionGardenZ_pointOnCurve core.(ActionGardenZ_inGdNew) /\
  ActionGardenZ_pointOnCurve core.(ActionGardenZ_inPkdNew).

Definition ActionGardenZ_actionBaseValuesTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inNk) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inRhoOld) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inPsiOld) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inVOld) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inAnchorPublic) /\
  ActionGardenZ_baseCanonical input.(ActionGardenZ_fullEnableSpend) /\
  ActionGardenZ_baseCanonical input.(ActionGardenZ_fullEnableOutput) /\
  ActionGardenZ_baseCanonical input.(ActionGardenZ_fullDisableCrossAddress) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inMagnitude) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inSign) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inLeaf) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inVNew) /\
  ActionGardenZ_baseCanonical core.(ActionGardenZ_inPsiNew).

Definition ActionGardenZ_actionScalarValuesTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  ActionGardenZ_scalarCanonical core.(ActionGardenZ_inRivk) /\
  ActionGardenZ_scalarCanonical core.(ActionGardenZ_inAlpha) /\
  ActionGardenZ_scalarCanonical input.(ActionGardenZ_fullRcmOld) /\
  ActionGardenZ_scalarCanonical core.(ActionGardenZ_inRcmNew) /\
  ActionGardenZ_scalarCanonical core.(ActionGardenZ_inRcv).

Definition ActionGardenZ_actionInputsTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  ActionGardenZ_actionPointsTyped input /\
  ActionGardenZ_actionBaseValuesTyped input /\
  ActionGardenZ_actionScalarValuesTyped input.

Definition ActionGardenZ_actionRangesValid (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  let twoTo64 := ActionGardenZ_zPowNat ActionGardenZ_zTwo 64%nat in
  let twoTo255 := ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat in
  ActionGardenZ_inRange core.(ActionGardenZ_inVOld) twoTo64 /\
  ActionGardenZ_inRange core.(ActionGardenZ_inVNew) twoTo64 /\
  ActionGardenZ_inRange core.(ActionGardenZ_inMagnitude) twoTo64 /\
  (core.(ActionGardenZ_inSign) = ActionGardenZ_zOne \/ core.(ActionGardenZ_inSign) = ActionGardenZ_baseNeg ActionGardenZ_zOne) /\
  ActionGardenZ_inRange core.(ActionGardenZ_inLeaf) twoTo255 /\
  forall element : ActionGardenZ_Z * ActionGardenZ_Z * bool,
    In element core.(ActionGardenZ_inPath) ->
    ActionGardenZ_inRange (snd (fst element)) twoTo255.

Definition ActionGardenZ_actionValueConstraints (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  ActionGardenZ_baseSub core.(ActionGardenZ_inVOld) core.(ActionGardenZ_inVNew) =
    ActionGardenZ_baseMul core.(ActionGardenZ_inMagnitude) core.(ActionGardenZ_inSign) /\
  ActionGardenZ_baseMul core.(ActionGardenZ_inVOld)
    (ActionGardenZ_baseSub ActionGardenZ_zOne input.(ActionGardenZ_fullEnableSpend)) = ActionGardenZ_zZero /\
  ActionGardenZ_baseMul core.(ActionGardenZ_inVNew)
    (ActionGardenZ_baseSub ActionGardenZ_zOne input.(ActionGardenZ_fullEnableOutput)) = ActionGardenZ_zZero /\
  (Not (input.(ActionGardenZ_fullDisableCrossAddress) = ActionGardenZ_zZero) ->
    core.(ActionGardenZ_inGdOld) = core.(ActionGardenZ_inGdNew) /\
    core.(ActionGardenZ_inPkdOld) = core.(ActionGardenZ_inPkdNew)).

Definition ActionGardenZ_actionOwnershipValid
    (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  let ivkWords :=
    ActionGardenZ_commitIvkMessageGarden (ActionGardenZ_extractXGarden core.(ActionGardenZ_inAk)) core.(ActionGardenZ_inNk) in
  let oldNoteWords :=
    ActionGardenZ_noteCommitMessageGarden core.(ActionGardenZ_inGdOld) core.(ActionGardenZ_inPkdOld)
      core.(ActionGardenZ_inVOld) core.(ActionGardenZ_inRhoOld) core.(ActionGardenZ_inPsiOld) in
  let ivkPoint :=
    ActionGardenZ_commitIvk parameters
      (ActionGardenZ_extractXGarden core.(ActionGardenZ_inAk)) core.(ActionGardenZ_inNk) core.(ActionGardenZ_inRivk) in
  ActionGardenZ_sinsemillaHashDefinedGarden
    parameters.(ActionGardenZ_paramsCommitIvkQ) ivkWords /\
  core.(ActionGardenZ_inPkdOld) =
    ActionGardenZ_scalarMul (ActionGardenZ_extractXGarden ivkPoint) core.(ActionGardenZ_inGdOld) /\
  ActionGardenZ_sinsemillaHashDefinedGarden
    parameters.(ActionGardenZ_paramsNoteCommitQ) oldNoteWords /\
  core.(ActionGardenZ_inCmOld) =
    ActionGardenZ_noteCommit parameters core.(ActionGardenZ_inGdOld) core.(ActionGardenZ_inPkdOld)
      core.(ActionGardenZ_inVOld) core.(ActionGardenZ_inRhoOld) core.(ActionGardenZ_inPsiOld)
      input.(ActionGardenZ_fullRcmOld).

Definition ActionGardenZ_actionMerkleValid
    (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  List.length core.(ActionGardenZ_inPath) = 32%nat /\
  ActionGardenZ_pathLayersCanonical core.(ActionGardenZ_inPath) /\
  ActionGardenZ_merklePathDefinedGarden parameters.(ActionGardenZ_paramsMerkleCrhQ)
    core.(ActionGardenZ_inLeaf) core.(ActionGardenZ_inPath) /\
  core.(ActionGardenZ_inLeaf) = ActionGardenZ_extractXGarden core.(ActionGardenZ_inCmOld) /\
  (core.(ActionGardenZ_inVOld) = ActionGardenZ_zZero \/
    core.(ActionGardenZ_inAnchorPublic) =
      ActionGardenZ_merkleRootGarden parameters.(ActionGardenZ_paramsMerkleCrhQ)
        core.(ActionGardenZ_inLeaf) core.(ActionGardenZ_inPath)).

Definition ActionGardenZ_actionNewNoteValid
    (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  let core := input.(ActionGardenZ_fullAction) in
  let nfOldValue :=
    ActionGardenZ_nullifier core.(ActionGardenZ_inNk) core.(ActionGardenZ_inRhoOld)
      core.(ActionGardenZ_inPsiOld) core.(ActionGardenZ_inCmOld) in
  ActionGardenZ_sinsemillaHashDefinedGarden parameters.(ActionGardenZ_paramsNoteCommitQ)
    (ActionGardenZ_noteCommitMessageGarden core.(ActionGardenZ_inGdNew) core.(ActionGardenZ_inPkdNew)
      core.(ActionGardenZ_inVNew) nfOldValue core.(ActionGardenZ_inPsiNew)).

Definition ActionGardenZ_validActionInputs
    (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  ActionGardenZ_actionParametersValid parameters /\
  ActionGardenZ_actionInputsTyped input /\
  ActionGardenZ_actionRangesValid input /\
  ActionGardenZ_actionValueConstraints input /\
  ActionGardenZ_actionOwnershipValid parameters input /\
  ActionGardenZ_actionMerkleValid parameters input /\
  ActionGardenZ_actionNewNoteValid parameters input.

Definition ActionGardenZ_orchardAction
    (parameters : ActionGardenZ_Params) (input : ActionGardenZ_ActionInputs) : ActionGardenZ_ActionOutputs :=
  let nfOldValue :=
    ActionGardenZ_nullifier input.(ActionGardenZ_inNk) input.(ActionGardenZ_inRhoOld)
      input.(ActionGardenZ_inPsiOld) input.(ActionGardenZ_inCmOld) in
  {|
    ActionGardenZ_outAnchor :=
      if ActionGardenZ_zEq input.(ActionGardenZ_inVOld) ActionGardenZ_zZero
      then input.(ActionGardenZ_inAnchorPublic)
      else
        ActionGardenZ_merkleRootGarden parameters.(ActionGardenZ_paramsMerkleCrhQ)
          input.(ActionGardenZ_inLeaf) input.(ActionGardenZ_inPath);
    ActionGardenZ_outCvNet :=
      ActionGardenZ_valueCommit
        (ActionGardenZ_signedNetValue input.(ActionGardenZ_inMagnitude) input.(ActionGardenZ_inSign))
        input.(ActionGardenZ_inRcv);
    ActionGardenZ_outNfOld := nfOldValue;
    ActionGardenZ_outRk := ActionGardenZ_spendAuthRandomize input.(ActionGardenZ_inAk) input.(ActionGardenZ_inAlpha);
    ActionGardenZ_outCmx :=
      ActionGardenZ_extractXGarden
        (ActionGardenZ_noteCommit parameters input.(ActionGardenZ_inGdNew) input.(ActionGardenZ_inPkdNew)
          input.(ActionGardenZ_inVNew) nfOldValue input.(ActionGardenZ_inPsiNew) input.(ActionGardenZ_inRcmNew))
  |}.
