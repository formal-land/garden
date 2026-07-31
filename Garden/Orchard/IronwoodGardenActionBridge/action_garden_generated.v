(** Generated from the axiom-free Lean ActionGarden.
    Lean source SHA-256: 731cb3b1ee03ad1a3f35e327aa0bc45078d551eaaff611610158719295131198

    This file is emitted from Lean's parser syntax tree by a closed,
    fail-closed translation. *)

From Stdlib Require Import ZArith List Bool Uint63 Array.PrimArray.
Require Export
  Garden.Orchard.IronwoodGardenActionBridge.action_garden_constants.
Import ListNotations.
Open Scope Z_scope.

Definition ActionGardenZ_Z : Type :=
  BinNums.Z.

Definition ActionGardenZ_pallasBaseModulus : ActionGardenZ_Z :=
  28948022309329048855892746252171976963363056481941560715954676764349967630337.

Definition ActionGardenZ_pallasScalarModulus : ActionGardenZ_Z :=
  28948022309329048855892746252171976963363056481941647379679742748393362948097.

Definition ActionGardenZ_zZero : ActionGardenZ_Z :=
  (Z.of_nat O).

Definition ActionGardenZ_zOne : ActionGardenZ_Z :=
  (Z.of_nat 1%nat).

Definition ActionGardenZ_zTwo : ActionGardenZ_Z :=
  (Z.of_nat 2%nat).

Definition ActionGardenZ_zAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (Z.add left right).

Definition ActionGardenZ_zSub (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (Z.sub left right).

Definition ActionGardenZ_zMul (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (Z.mul left right).

Definition ActionGardenZ_zNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (Z.opp value).

Definition ActionGardenZ_zDiv (dividend divisor : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (match divisor with | Zneg magnitude => Z.opp (Z.div dividend (Z.pos magnitude)) | _ => Z.div dividend divisor end).

Definition ActionGardenZ_zMod (dividend modulus : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (match modulus with | Zneg magnitude => Z.modulo dividend (Z.pos magnitude) | _ => Z.modulo dividend modulus end).

Definition ActionGardenZ_zPowNat (base : ActionGardenZ_Z) (exponent : nat) : ActionGardenZ_Z :=
  (Z.pow base (Z.of_nat exponent)).

Definition ActionGardenZ_zEq (left right : ActionGardenZ_Z) : bool :=
  (Z.eqb left right).

Definition ActionGardenZ_inRange (value upperBound : ActionGardenZ_Z) : Prop :=
  ((Z.le ActionGardenZ_zZero value) /\ (Z.lt value upperBound)).

Definition ActionGardenZ_normalize (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_zMod value modulus).

Definition ActionGardenZ_addModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize modulus (ActionGardenZ_zAdd left right)).

Definition ActionGardenZ_subModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize modulus (ActionGardenZ_zSub left right)).

Definition ActionGardenZ_mulModulo (modulus left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize modulus (ActionGardenZ_zMul left right)).

Definition ActionGardenZ_negModulo (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize modulus (ActionGardenZ_zNeg value)).

Definition ActionGardenZ_baseNormalize (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize ActionGardenZ_pallasBaseModulus value).

Definition ActionGardenZ_baseAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_addModulo ActionGardenZ_pallasBaseModulus left right).

Definition ActionGardenZ_baseSub (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_subModulo ActionGardenZ_pallasBaseModulus left right).

Definition ActionGardenZ_baseMul (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_mulModulo ActionGardenZ_pallasBaseModulus left right).

Definition ActionGardenZ_baseNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_negModulo ActionGardenZ_pallasBaseModulus value).

Definition ActionGardenZ_baseEqual (left right : ActionGardenZ_Z) : bool :=
  (ActionGardenZ_zEq (ActionGardenZ_baseNormalize left) (ActionGardenZ_baseNormalize right)).

Definition ActionGardenZ_baseCanonical (value : ActionGardenZ_Z) : Prop :=
  ((ActionGardenZ_baseNormalize value) = value).

Definition ActionGardenZ_scalarNormalize (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_normalize ActionGardenZ_pallasScalarModulus value).

Definition ActionGardenZ_scalarAdd (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_addModulo ActionGardenZ_pallasScalarModulus left right).

Definition ActionGardenZ_scalarNeg (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_negModulo ActionGardenZ_pallasScalarModulus value).

Definition ActionGardenZ_scalarCanonical (value : ActionGardenZ_Z) : Prop :=
  ((ActionGardenZ_scalarNormalize value) = value).

Definition ActionGardenZ_baseToScalar (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_scalarNormalize (ActionGardenZ_baseNormalize value)).

Definition ActionGardenZ_modInverse (modulus value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (let reduced := (ActionGardenZ_normalize modulus value) in (if (ActionGardenZ_zEq reduced ActionGardenZ_zZero) then ActionGardenZ_zZero else (ActionGardenZ_normalize modulus (ActionGardenZ_zPowNat reduced (Z.to_nat (ActionGardenZ_zSub modulus ActionGardenZ_zTwo)))))).

Definition ActionGardenZ_baseInverse (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_modInverse ActionGardenZ_pallasBaseModulus value).

Definition ActionGardenZ_baseDiv (numerator denominator : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (ActionGardenZ_baseMul numerator (ActionGardenZ_baseInverse denominator)).

Definition ActionGardenZ_Point : Type := ActionGardenPointData.

Definition ActionGardenZ_pointIdentity : ActionGardenZ_Point :=
  {| actionGardenPointX := ActionGardenZ_zZero; actionGardenPointY := ActionGardenZ_zZero |}.

Definition ActionGardenZ_pointNormalize (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  {| actionGardenPointX := (ActionGardenZ_baseNormalize (actionGardenPointX point)); actionGardenPointY := (ActionGardenZ_baseNormalize (actionGardenPointY point)) |}.

Definition ActionGardenZ_pointIsIdentity (point : ActionGardenZ_Point) : bool :=
  (andb (ActionGardenZ_baseEqual (actionGardenPointX point) ActionGardenZ_zZero) (ActionGardenZ_baseEqual (actionGardenPointY point) ActionGardenZ_zZero)).

Definition ActionGardenZ_pointCanonical (point : ActionGardenZ_Point) : Prop :=
  ((ActionGardenZ_baseCanonical (actionGardenPointX point)) /\ (ActionGardenZ_baseCanonical (actionGardenPointY point))).

Definition ActionGardenZ_pointOnCurve (point : ActionGardenZ_Point) : Prop :=
  (let xSquared := (ActionGardenZ_baseMul (actionGardenPointX point) (actionGardenPointX point)) in (let xCubed := (ActionGardenZ_baseMul xSquared (actionGardenPointX point)) in (let right := (ActionGardenZ_baseAdd xCubed (Z.of_nat 5%nat)) in ((ActionGardenZ_baseMul (actionGardenPointY point) (actionGardenPointY point)) = right)))).

Definition ActionGardenZ_pointValid (point : ActionGardenZ_Point) : Prop :=
  (((ActionGardenZ_pointNormalize point) = ActionGardenZ_pointIdentity) \/ (ActionGardenZ_pointOnCurve point)).

Definition ActionGardenZ_pointNeg (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (if (ActionGardenZ_pointIsIdentity point) then ActionGardenZ_pointIdentity else {| actionGardenPointX := (ActionGardenZ_baseNormalize (actionGardenPointX point)); actionGardenPointY := (ActionGardenZ_baseNeg (actionGardenPointY point)) |}).

Definition ActionGardenZ_pointAdd (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (if (ActionGardenZ_pointIsIdentity left) then (ActionGardenZ_pointNormalize right) else (if (ActionGardenZ_pointIsIdentity right) then (ActionGardenZ_pointNormalize left) else (if (ActionGardenZ_baseEqual (actionGardenPointX left) (actionGardenPointX right)) then (if (ActionGardenZ_baseEqual (ActionGardenZ_baseAdd (actionGardenPointY left) (actionGardenPointY right)) ActionGardenZ_zZero) then ActionGardenZ_pointIdentity else (let numerator := (ActionGardenZ_baseAdd (ActionGardenZ_baseMul (Z.of_nat 3%nat) (ActionGardenZ_baseMul (actionGardenPointX left) (actionGardenPointX left))) ActionGardenZ_zZero) in (let denominator := (ActionGardenZ_baseMul ActionGardenZ_zTwo (actionGardenPointY left)) in (let slope := (ActionGardenZ_baseDiv numerator denominator) in (let resultX := (ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) (actionGardenPointX left)) (actionGardenPointX right)) in (let resultY := (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub (actionGardenPointX left) resultX)) (actionGardenPointY left)) in {| actionGardenPointX := resultX; actionGardenPointY := resultY |})))))) else (let numerator := (ActionGardenZ_baseSub (actionGardenPointY right) (actionGardenPointY left)) in (let denominator := (ActionGardenZ_baseSub (actionGardenPointX right) (actionGardenPointX left)) in (let slope := (ActionGardenZ_baseDiv numerator denominator) in (let resultX := (ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) (actionGardenPointX left)) (actionGardenPointX right)) in (let resultY := (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub (actionGardenPointX left) resultX)) (actionGardenPointY left)) in {| actionGardenPointX := resultX; actionGardenPointY := resultY |})))))))).

Fixpoint ActionGardenZ_pointNatMul (scalar : nat) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  match scalar, point with | O, _ => ActionGardenZ_pointIdentity | S scalar, point => (ActionGardenZ_pointAdd (ActionGardenZ_pointNatMul scalar point) point) end.

Definition ActionGardenZ_scalarMul (scalar : ActionGardenZ_Z) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (ActionGardenZ_pointNatMul (Z.to_nat (ActionGardenZ_scalarNormalize scalar)) point).

Definition ActionGardenZ_basePointMul (baseValue : ActionGardenZ_Z) (point : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (ActionGardenZ_pointNatMul (Z.to_nat (ActionGardenZ_baseNormalize baseValue)) point).

Definition ActionGardenZ_extractX (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  (if (ActionGardenZ_pointIsIdentity point) then ActionGardenZ_zZero else (ActionGardenZ_baseNormalize (actionGardenPointX point))).

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
  ActionGardenZ_m22 : ActionGardenZ_Z
}.

Record ActionGardenZ_PoseidonParameters : Type := {
  ActionGardenZ_roundConstant : ActionGardenZ_Z -> ActionGardenZ_State3;
  ActionGardenZ_mds : ActionGardenZ_Matrix3
}.

Definition ActionGardenZ_basePow5 (value : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (let square := (ActionGardenZ_baseMul value value) in (ActionGardenZ_baseMul (ActionGardenZ_baseMul square square) value)).

Definition ActionGardenZ_matrixApply (matrix : ActionGardenZ_Matrix3) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  {| ActionGardenZ_x0 := (ActionGardenZ_baseAdd (ActionGardenZ_baseAdd (ActionGardenZ_baseMul (ActionGardenZ_x0 state) (ActionGardenZ_m00 matrix)) (ActionGardenZ_baseMul (ActionGardenZ_x1 state) (ActionGardenZ_m01 matrix))) (ActionGardenZ_baseMul (ActionGardenZ_x2 state) (ActionGardenZ_m02 matrix))); ActionGardenZ_x1 := (ActionGardenZ_baseAdd (ActionGardenZ_baseAdd (ActionGardenZ_baseMul (ActionGardenZ_x0 state) (ActionGardenZ_m10 matrix)) (ActionGardenZ_baseMul (ActionGardenZ_x1 state) (ActionGardenZ_m11 matrix))) (ActionGardenZ_baseMul (ActionGardenZ_x2 state) (ActionGardenZ_m12 matrix))); ActionGardenZ_x2 := (ActionGardenZ_baseAdd (ActionGardenZ_baseAdd (ActionGardenZ_baseMul (ActionGardenZ_x0 state) (ActionGardenZ_m20 matrix)) (ActionGardenZ_baseMul (ActionGardenZ_x1 state) (ActionGardenZ_m21 matrix))) (ActionGardenZ_baseMul (ActionGardenZ_x2 state) (ActionGardenZ_m22 matrix))) |}.

Definition ActionGardenZ_poseidonFullRound (parameters : ActionGardenZ_PoseidonParameters) (round : ActionGardenZ_Z) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  (let constants := ((ActionGardenZ_roundConstant parameters) round) in (ActionGardenZ_matrixApply (ActionGardenZ_mds parameters) {| ActionGardenZ_x0 := (ActionGardenZ_basePow5 (ActionGardenZ_baseAdd (ActionGardenZ_x0 state) (ActionGardenZ_x0 constants))); ActionGardenZ_x1 := (ActionGardenZ_basePow5 (ActionGardenZ_baseAdd (ActionGardenZ_x1 state) (ActionGardenZ_x1 constants))); ActionGardenZ_x2 := (ActionGardenZ_basePow5 (ActionGardenZ_baseAdd (ActionGardenZ_x2 state) (ActionGardenZ_x2 constants))) |})).

Definition ActionGardenZ_poseidonPartialPair (parameters : ActionGardenZ_PoseidonParameters) (round : ActionGardenZ_Z) (state : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  (let firstConstants := ((ActionGardenZ_roundConstant parameters) round) in (let firstMixed := (ActionGardenZ_matrixApply (ActionGardenZ_mds parameters) {| ActionGardenZ_x0 := (ActionGardenZ_basePow5 (ActionGardenZ_baseAdd (ActionGardenZ_x0 state) (ActionGardenZ_x0 firstConstants))); ActionGardenZ_x1 := (ActionGardenZ_baseAdd (ActionGardenZ_x1 state) (ActionGardenZ_x1 firstConstants)); ActionGardenZ_x2 := (ActionGardenZ_baseAdd (ActionGardenZ_x2 state) (ActionGardenZ_x2 firstConstants)) |}) in (let secondConstants := ((ActionGardenZ_roundConstant parameters) (ActionGardenZ_zAdd round ActionGardenZ_zOne)) in (ActionGardenZ_matrixApply (ActionGardenZ_mds parameters) {| ActionGardenZ_x0 := (ActionGardenZ_basePow5 (ActionGardenZ_baseAdd (ActionGardenZ_x0 firstMixed) (ActionGardenZ_x0 secondConstants))); ActionGardenZ_x1 := (ActionGardenZ_baseAdd (ActionGardenZ_x1 firstMixed) (ActionGardenZ_x1 secondConstants)); ActionGardenZ_x2 := (ActionGardenZ_baseAdd (ActionGardenZ_x2 firstMixed) (ActionGardenZ_x2 secondConstants)) |})))).

Fixpoint ActionGardenZ_iterateIndexedFrom {A : Type} (count : nat) (index : nat) (step : nat -> A -> A) (initial : A) : A :=
  (match count with | O => initial | S remaining => (ActionGardenZ_iterateIndexedFrom remaining (S index) step (step index initial)) end).

Definition ActionGardenZ_iterateIndexed {A : Type} (count : nat) (step : nat -> A -> A) (initial : A) : A :=
  (ActionGardenZ_iterateIndexedFrom count O step initial).

Definition ActionGardenZ_poseidonPermute (parameters : ActionGardenZ_PoseidonParameters) (initial : ActionGardenZ_State3) : ActionGardenZ_State3 :=
  (let afterFirstFull := (ActionGardenZ_iterateIndexed 4%nat (fun index state => (ActionGardenZ_poseidonFullRound parameters (Z.of_nat index) state)) initial) in (let afterPartial := (ActionGardenZ_iterateIndexed 28%nat (fun index state => (ActionGardenZ_poseidonPartialPair parameters (Z.of_nat (Nat.add 4%nat (Nat.mul 2%nat index))) state)) afterFirstFull) in (ActionGardenZ_iterateIndexed 4%nat (fun index state => (ActionGardenZ_poseidonFullRound parameters (Z.of_nat (Nat.add 60%nat index)) state)) afterPartial))).

Definition ActionGardenZ_poseidonHash2 (parameters : ActionGardenZ_PoseidonParameters) (left right : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (let capacity := (ActionGardenZ_baseNormalize (ActionGardenZ_zMul (Z.of_nat 2%nat) (ActionGardenZ_zPowNat (Z.of_nat 2%nat) 64%nat))) in (ActionGardenZ_x0 (ActionGardenZ_poseidonPermute parameters {| ActionGardenZ_x0 := left; ActionGardenZ_x1 := right; ActionGardenZ_x2 := capacity |}))).

Definition ActionGardenZ_listGetDAtZ {A : Type} (values : PrimArray.array A) (index : ActionGardenZ_Z) (fallback : A) : A :=
  let normalizedIndex := Z.max ActionGardenZ_zZero index in
  if Z.ltb normalizedIndex (Uint63.to_Z (PrimArray.length values)) then
    PrimArray.get values (Uint63.of_Z normalizedIndex)
  else fallback.

Definition ActionGardenZ_orchardPoseidonRoundConstants : PrimArray.array ActionGardenZ_State3 := actionGardenPoseidonRoundConstantsData.

Definition ActionGardenZ_orchardPoseidonRoundConstant (round : ActionGardenZ_Z) : ActionGardenZ_State3 :=
  (ActionGardenZ_listGetDAtZ ActionGardenZ_orchardPoseidonRoundConstants round (Build_ActionGardenState3Data ActionGardenZ_zZero ActionGardenZ_zZero ActionGardenZ_zZero)).

Definition ActionGardenZ_orchardPoseidonMds : ActionGardenZ_Matrix3 :=
  {| ActionGardenZ_m00 := 4844513277385895547578596669280046666372576567380472439333234012806535256931; ActionGardenZ_m01 := 22420227485671588580194914215361958133919537309433003325602272145024023440222; ActionGardenZ_m02 := 3505906565384614297249013623188452104971681200991017471148427242055139865693; ActionGardenZ_m10 := 15918204248318370126242808206081613758525089148509539575126649371340283647612; ActionGardenZ_m11 := 17094040714843518372934853765548613673798971581804674915582475057795168500270; ActionGardenZ_m12 := 15812769689003694604229247543370933348074043003262912834067271177893884949626; ActionGardenZ_m20 := 20880359470746774736726481852287259022559450533689220298394450009637377072100; ActionGardenZ_m21 := 13164192954509875252051728398669721690665762613581286296450591265062029506148; ActionGardenZ_m22 := 27123552791154096240274588421608257979835967097480491934880175221940903501553 |}.

Definition ActionGardenZ_orchardPoseidonParameters : ActionGardenZ_PoseidonParameters :=
  {| ActionGardenZ_roundConstant := ActionGardenZ_orchardPoseidonRoundConstant; ActionGardenZ_mds := ActionGardenZ_orchardPoseidonMds |}.

Definition ActionGardenZ_orchardSinsemillaGenerators : PrimArray.array ActionGardenZ_Point := actionGardenSinsemillaGeneratorsData.

Definition ActionGardenZ_orchardSinsemillaGenerator (chunk : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_listGetDAtZ ActionGardenZ_orchardSinsemillaGenerators chunk ActionGardenZ_pointIdentity).

Definition ActionGardenZ_orchardNoteCommitQ : ActionGardenZ_Point :=
  {| actionGardenPointX := 10629404576683096409262958701336170057000067777256141967953463442979689100381; actionGardenPointY := 22898949290933268079297281211505753011910178734473470279111609228438645877859 |}.

Definition ActionGardenZ_orchardCommitIvkQ : ActionGardenZ_Point :=
  {| actionGardenPointX := 2593820817260930114322133467408868473290945477826616247349533151445648376562; actionGardenPointY := 12214744946019415453501880094709511126888074367290315326445800415816181472958 |}.

Definition ActionGardenZ_orchardMerkleCrhQ : ActionGardenZ_Point :=
  {| actionGardenPointX := 9991206725476878888751475603038274618448000607209514551456795194094072219296; actionGardenPointY := 24209798415301550423396126020228723009317736024280831393239261884225294625378 |}.

Definition ActionGardenZ_orchardSpendAuthG : ActionGardenZ_Point :=
  {| actionGardenPointX := 25027635063850382358429654596649554085117301901282348152423547104939793041763; actionGardenPointY := 12128007492603938773365931378340937928001494939630793217712875072231079427017 |}.

Definition ActionGardenZ_orchardValueCommitVG : ActionGardenZ_Point :=
  {| actionGardenPointX := 21457208314186520936880902219424053485005045883401337627148481900742711001959; actionGardenPointY := 20379375922573002911833717643813254676246486412159279022689151936901102105230 |}.

Definition ActionGardenZ_orchardValueCommitRG : ActionGardenZ_Point :=
  {| actionGardenPointX := 3597772235883004661259329170144280297379687592370687591147658848249887611537; actionGardenPointY := 16317546749781193797530044795837656238506071957562073482938086095508632426954 |}.

Definition ActionGardenZ_orchardNullifierKG : ActionGardenZ_Point :=
  {| actionGardenPointX := 17144890976040313974462754624161095328261290075490099718273142830262355741301; actionGardenPointY := 9661337292872073193100428608853316471968232023361741282759000480983323509196 |}.

Definition ActionGardenZ_orchardNoteCommitRG : ActionGardenZ_Point :=
  {| actionGardenPointX := 17502433695644481444785977856966854265310331039772160001849803703443502427667; actionGardenPointY := 27531606546556235994383748883097777001194017792923801570415255878186539366371 |}.

Definition ActionGardenZ_orchardCommitIvkRG : ActionGardenZ_Point :=
  {| actionGardenPointX := 17022113834174368664964072539940476916905682548990455171271428285673934201112; actionGardenPointY := 18912017636736613471143674001158885358143653198146604093009134371854861983145 |}.

Record ActionGardenZ_Params : Type := {
  ActionGardenZ_paramsNoteCommitQ : ActionGardenZ_Point;
  ActionGardenZ_paramsCommitIvkQ : ActionGardenZ_Point;
  ActionGardenZ_paramsMerkleCrhQ : ActionGardenZ_Point
}.

Definition ActionGardenZ_orchardParams : ActionGardenZ_Params :=
  {| ActionGardenZ_paramsNoteCommitQ := ActionGardenZ_orchardNoteCommitQ; ActionGardenZ_paramsCommitIvkQ := ActionGardenZ_orchardCommitIvkQ; ActionGardenZ_paramsMerkleCrhQ := ActionGardenZ_orchardMerkleCrhQ |}.

Definition ActionGardenZ_pointAddGarden (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (if (ActionGardenZ_zEq (actionGardenPointX left) ActionGardenZ_zZero) then right else (if (ActionGardenZ_zEq (actionGardenPointX right) ActionGardenZ_zZero) then left else (if (andb (ActionGardenZ_zEq (actionGardenPointX left) (actionGardenPointX right)) (ActionGardenZ_zEq (ActionGardenZ_baseAdd (actionGardenPointY left) (actionGardenPointY right)) ActionGardenZ_zZero)) then ActionGardenZ_pointIdentity else (let slope := (if (ActionGardenZ_zEq (actionGardenPointX left) (actionGardenPointX right)) then (ActionGardenZ_baseDiv (ActionGardenZ_baseMul (Z.of_nat 3%nat) (ActionGardenZ_baseMul (actionGardenPointX left) (actionGardenPointX left))) (ActionGardenZ_baseMul ActionGardenZ_zTwo (actionGardenPointY left))) else (ActionGardenZ_baseDiv (ActionGardenZ_baseSub (actionGardenPointY right) (actionGardenPointY left)) (ActionGardenZ_baseSub (actionGardenPointX right) (actionGardenPointX left)))) in (let x := (ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) (actionGardenPointX left)) (actionGardenPointX right)) in {| actionGardenPointX := x; actionGardenPointY := (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub (actionGardenPointX left) x)) (actionGardenPointY left)) |}))))).

Definition ActionGardenZ_extractXGarden (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  (actionGardenPointX point).

Definition ActionGardenZ_pointAddIncomplete (left right : ActionGardenZ_Point) : ActionGardenZ_Point :=
  (let slope := (ActionGardenZ_baseDiv (ActionGardenZ_baseSub (actionGardenPointY left) (actionGardenPointY right)) (ActionGardenZ_baseSub (actionGardenPointX left) (actionGardenPointX right))) in (let x := (ActionGardenZ_baseSub (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope slope) (actionGardenPointX left)) (actionGardenPointX right)) in {| actionGardenPointX := x; actionGardenPointY := (ActionGardenZ_baseSub (ActionGardenZ_baseMul slope (ActionGardenZ_baseSub (actionGardenPointX left) x)) (actionGardenPointY left)) |})).

Definition ActionGardenZ_sinsemillaRound (accumulator : ActionGardenZ_Point) (word : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_pointAddIncomplete (ActionGardenZ_pointAddIncomplete accumulator (ActionGardenZ_orchardSinsemillaGenerator word)) accumulator).

Definition ActionGardenZ_sinsemillaHashToPointGarden (domain : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : ActionGardenZ_Point :=
  (fold_left ActionGardenZ_sinsemillaRound words domain).

Definition ActionGardenZ_pointIdentityGarden (point : ActionGardenZ_Point) : Prop :=
  (((actionGardenPointX point) = ActionGardenZ_zZero) /\ ((actionGardenPointY point) = ActionGardenZ_zZero)).

Definition ActionGardenZ_sinsemillaRoundDefined (accumulator : ActionGardenZ_Point) (word : ActionGardenZ_Z) : Prop :=
  (let generator := (ActionGardenZ_orchardSinsemillaGenerator word) in (let firstSum := (ActionGardenZ_pointAddIncomplete accumulator generator) in ((not (ActionGardenZ_pointIdentityGarden accumulator)) /\ ((not (ActionGardenZ_pointIdentityGarden generator)) /\ ((not ((ActionGardenZ_baseNormalize (actionGardenPointX accumulator)) = (ActionGardenZ_baseNormalize (actionGardenPointX generator)))) /\ ((not (ActionGardenZ_pointIdentityGarden firstSum)) /\ (not ((ActionGardenZ_baseNormalize (actionGardenPointX firstSum)) = (ActionGardenZ_baseNormalize (actionGardenPointX accumulator)))))))))).

Fixpoint ActionGardenZ_sinsemillaHashDefinedFromGarden (accumulator : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : Prop :=
  match accumulator, words with | _, nil => True | accumulator, cons word rest => ((ActionGardenZ_sinsemillaRoundDefined accumulator word) /\ (ActionGardenZ_sinsemillaHashDefinedFromGarden (ActionGardenZ_sinsemillaRound accumulator word) rest)) end.

Definition ActionGardenZ_sinsemillaHashDefinedGarden (domain : ActionGardenZ_Point) (words : list ActionGardenZ_Z) : Prop :=
  (ActionGardenZ_sinsemillaHashDefinedFromGarden domain words).

Fixpoint ActionGardenZ_wordsLe (count : nat) (value : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  match count, value with | O, _ => nil | S count, value => (cons (ActionGardenZ_zMod value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat)) (ActionGardenZ_wordsLe count (ActionGardenZ_zDiv value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat)))) end.

Definition ActionGardenZ_pointParity (point : ActionGardenZ_Point) : ActionGardenZ_Z :=
  (ActionGardenZ_zMod (actionGardenPointY point) ActionGardenZ_zTwo).

Definition ActionGardenZ_noteCommitMessageGarden (gd pkd : ActionGardenZ_Point) (value rho psi : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  (ActionGardenZ_wordsLe 109%nat (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_zAdd (ActionGardenZ_extractXGarden gd) (ActionGardenZ_zMul (ActionGardenZ_pointParity gd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat))) (ActionGardenZ_zMul (ActionGardenZ_extractXGarden pkd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 256%nat))) (ActionGardenZ_zMul (ActionGardenZ_pointParity pkd) (ActionGardenZ_zPowNat ActionGardenZ_zTwo 511%nat))) (ActionGardenZ_zMul value (ActionGardenZ_zPowNat ActionGardenZ_zTwo 512%nat))) (ActionGardenZ_zMul rho (ActionGardenZ_zPowNat ActionGardenZ_zTwo 576%nat))) (ActionGardenZ_zMul psi (ActionGardenZ_zPowNat ActionGardenZ_zTwo 831%nat))) ActionGardenZ_zZero) ActionGardenZ_zZero)).

Definition ActionGardenZ_commitIvkMessageGarden (ak nk : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  (ActionGardenZ_wordsLe 51%nat (ActionGardenZ_zAdd ak (ActionGardenZ_zMul nk (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat)))).

Definition ActionGardenZ_merkleMessageGarden (layer left right : ActionGardenZ_Z) : list ActionGardenZ_Z :=
  (ActionGardenZ_wordsLe 52%nat (ActionGardenZ_zAdd layer (ActionGardenZ_zAdd (ActionGardenZ_zMul left (ActionGardenZ_zPowNat ActionGardenZ_zTwo 10%nat)) (ActionGardenZ_zMul right (ActionGardenZ_zPowNat ActionGardenZ_zTwo 265%nat))))).

Definition ActionGardenZ_merkleLayer (domain : ActionGardenZ_Point) (layer node sibling : ActionGardenZ_Z) (isRight : bool) : ActionGardenZ_Z :=
  (let left := (if isRight then sibling else node) in (let right := (if isRight then node else sibling) in (ActionGardenZ_extractXGarden (ActionGardenZ_sinsemillaHashToPointGarden domain (ActionGardenZ_merkleMessageGarden layer left right))))).

Definition ActionGardenZ_merkleRootGarden (domain : ActionGardenZ_Point) (leaf : ActionGardenZ_Z) (path : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) : ActionGardenZ_Z :=
  (fold_left (fun node element => (ActionGardenZ_merkleLayer domain (fst (fst element)) node (snd (fst element)) (snd element))) path leaf).

Definition ActionGardenZ_merkleStepDefinedGarden (domain : ActionGardenZ_Point) (node layer sibling : ActionGardenZ_Z) (isRight : bool) : Prop :=
  (let left := (if isRight then sibling else node) in (let right := (if isRight then node else sibling) in (ActionGardenZ_sinsemillaHashDefinedGarden domain (ActionGardenZ_merkleMessageGarden layer left right)))).

Inductive ActionGardenZ_merklePathDefinedFromGarden (domain : ActionGardenZ_Point) : ActionGardenZ_Z -> (list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) -> Prop :=
  | ActionGardenMerklePathDefinedNil (node : ActionGardenZ_Z) : (ActionGardenZ_merklePathDefinedFromGarden domain node nil)
  | ActionGardenMerklePathDefinedCons (node nextNode layer sibling : ActionGardenZ_Z) (isRight : bool) (rest : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) : ((ActionGardenZ_merkleStepDefinedGarden domain node layer sibling isRight) -> ((nextNode = (ActionGardenZ_merkleLayer domain layer node sibling isRight)) -> ((ActionGardenZ_merklePathDefinedFromGarden domain nextNode rest) -> (ActionGardenZ_merklePathDefinedFromGarden domain node (cons ((layer, sibling), isRight) rest))))).

Definition ActionGardenZ_merklePathDefinedGarden (domain : ActionGardenZ_Point) (leaf : ActionGardenZ_Z) (path : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) : Prop :=
  (ActionGardenZ_merklePathDefinedFromGarden domain leaf path).

Fixpoint ActionGardenZ_pathLayersFrom (expected : ActionGardenZ_Z) (path : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) : Prop :=
  match expected, path with | _, nil => True | expected, cons element rest => (((fst (fst element)) = expected) /\ (ActionGardenZ_pathLayersFrom (ActionGardenZ_zAdd expected ActionGardenZ_zOne) rest)) end.

Definition ActionGardenZ_pathLayersCanonical (path : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool)) : Prop :=
  (ActionGardenZ_pathLayersFrom ActionGardenZ_zZero path).

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
  ActionGardenZ_inPath : list ((ActionGardenZ_Z * ActionGardenZ_Z) * bool);
  ActionGardenZ_inGdNew : ActionGardenZ_Point;
  ActionGardenZ_inPkdNew : ActionGardenZ_Point;
  ActionGardenZ_inVNew : ActionGardenZ_Z;
  ActionGardenZ_inPsiNew : ActionGardenZ_Z;
  ActionGardenZ_inRcmNew : ActionGardenZ_Z
}.

Record ActionGardenZ_FullActionInputs : Type := {
  ActionGardenZ_fullAction : ActionGardenZ_ActionInputs;
  ActionGardenZ_fullRcmOld : ActionGardenZ_Z;
  ActionGardenZ_fullEnableSpend : ActionGardenZ_Z;
  ActionGardenZ_fullEnableOutput : ActionGardenZ_Z;
  ActionGardenZ_fullDisableCrossAddress : ActionGardenZ_Z
}.

Record ActionGardenZ_ActionOutputs : Type := {
  ActionGardenZ_outAnchor : ActionGardenZ_Z;
  ActionGardenZ_outCvNet : ActionGardenZ_Point;
  ActionGardenZ_outNfOld : ActionGardenZ_Z;
  ActionGardenZ_outRk : ActionGardenZ_Point;
  ActionGardenZ_outCmx : ActionGardenZ_Z
}.

Definition ActionGardenZ_signedNetValue (magnitude sign : ActionGardenZ_Z) : ActionGardenZ_Z :=
  (if (ActionGardenZ_zEq sign ActionGardenZ_zOne) then magnitude else (ActionGardenZ_zNeg magnitude)).

Definition ActionGardenZ_spendAuthRandomize (ak : ActionGardenZ_Point) (alpha : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_pointAddGarden ak (ActionGardenZ_scalarMul alpha ActionGardenZ_orchardSpendAuthG)).

Definition ActionGardenZ_valueCommit (value randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_pointAddGarden (ActionGardenZ_scalarMul value ActionGardenZ_orchardValueCommitVG) (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardValueCommitRG)).

Definition ActionGardenZ_nullifier (nk rho psi : ActionGardenZ_Z) (cm : ActionGardenZ_Point) : ActionGardenZ_Z :=
  (let hash := (ActionGardenZ_poseidonHash2 ActionGardenZ_orchardPoseidonParameters nk rho) in (let scalar := (ActionGardenZ_baseAdd hash psi) in (ActionGardenZ_extractXGarden (ActionGardenZ_pointAddGarden (ActionGardenZ_scalarMul scalar ActionGardenZ_orchardNullifierKG) cm)))).

Definition ActionGardenZ_noteCommit (parameters : ActionGardenZ_Params) (gd pkd : ActionGardenZ_Point) (value rho psi randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_pointAddGarden (ActionGardenZ_sinsemillaHashToPointGarden (ActionGardenZ_paramsNoteCommitQ parameters) (ActionGardenZ_noteCommitMessageGarden gd pkd value rho psi)) (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardNoteCommitRG)).

Definition ActionGardenZ_commitIvk (parameters : ActionGardenZ_Params) (ak nk randomness : ActionGardenZ_Z) : ActionGardenZ_Point :=
  (ActionGardenZ_pointAddGarden (ActionGardenZ_sinsemillaHashToPointGarden (ActionGardenZ_paramsCommitIvkQ parameters) (ActionGardenZ_commitIvkMessageGarden ak nk)) (ActionGardenZ_scalarMul randomness ActionGardenZ_orchardCommitIvkRG)).

Definition ActionGardenZ_actionParametersValid (parameters : ActionGardenZ_Params) : Prop :=
  ((ActionGardenZ_pointCanonical (ActionGardenZ_paramsNoteCommitQ parameters)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_paramsCommitIvkQ parameters)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_paramsMerkleCrhQ parameters)) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardSpendAuthG) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardValueCommitVG) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardValueCommitRG) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardNullifierKG) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardNoteCommitRG) /\ ((ActionGardenZ_pointCanonical ActionGardenZ_orchardCommitIvkRG) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_paramsNoteCommitQ parameters)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_paramsCommitIvkQ parameters)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_paramsMerkleCrhQ parameters)) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardSpendAuthG) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardValueCommitVG) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardValueCommitRG) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardNullifierKG) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardNoteCommitRG) /\ ((ActionGardenZ_pointOnCurve ActionGardenZ_orchardCommitIvkRG) /\ (forall word : ActionGardenZ_Z, ((ActionGardenZ_inRange word (Z.of_nat 1024%nat)) -> ((ActionGardenZ_pointCanonical (ActionGardenZ_orchardSinsemillaGenerator word)) /\ (ActionGardenZ_pointOnCurve (ActionGardenZ_orchardSinsemillaGenerator word))))))))))))))))))))))).

Definition ActionGardenZ_actionPointsTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in ((ActionGardenZ_pointCanonical (ActionGardenZ_inAk core)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_inCmOld core)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_inGdOld core)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_inPkdOld core)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_inGdNew core)) /\ ((ActionGardenZ_pointCanonical (ActionGardenZ_inPkdNew core)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_inAk core)) /\ ((ActionGardenZ_pointValid (ActionGardenZ_inCmOld core)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_inGdOld core)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_inPkdOld core)) /\ ((ActionGardenZ_pointOnCurve (ActionGardenZ_inGdNew core)) /\ (ActionGardenZ_pointOnCurve (ActionGardenZ_inPkdNew core)))))))))))))).

Definition ActionGardenZ_actionBaseValuesTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in ((ActionGardenZ_baseCanonical (ActionGardenZ_inNk core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inRhoOld core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inPsiOld core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inVOld core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inAnchorPublic core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_fullEnableSpend input)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_fullEnableOutput input)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_fullDisableCrossAddress input)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inMagnitude core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inSign core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inLeaf core)) /\ ((ActionGardenZ_baseCanonical (ActionGardenZ_inVNew core)) /\ (ActionGardenZ_baseCanonical (ActionGardenZ_inPsiNew core))))))))))))))).

Definition ActionGardenZ_actionScalarValuesTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in ((ActionGardenZ_scalarCanonical (ActionGardenZ_inRivk core)) /\ ((ActionGardenZ_scalarCanonical (ActionGardenZ_inAlpha core)) /\ ((ActionGardenZ_scalarCanonical (ActionGardenZ_fullRcmOld input)) /\ ((ActionGardenZ_scalarCanonical (ActionGardenZ_inRcmNew core)) /\ (ActionGardenZ_scalarCanonical (ActionGardenZ_inRcv core))))))).

Definition ActionGardenZ_actionInputsTyped (input : ActionGardenZ_FullActionInputs) : Prop :=
  ((ActionGardenZ_actionPointsTyped input) /\ ((ActionGardenZ_actionBaseValuesTyped input) /\ (ActionGardenZ_actionScalarValuesTyped input))).

Definition ActionGardenZ_actionRangesValid (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in (let twoTo64 := (ActionGardenZ_zPowNat ActionGardenZ_zTwo 64%nat) in (let twoTo255 := (ActionGardenZ_zPowNat ActionGardenZ_zTwo 255%nat) in ((ActionGardenZ_inRange (ActionGardenZ_inVOld core) twoTo64) /\ ((ActionGardenZ_inRange (ActionGardenZ_inVNew core) twoTo64) /\ ((ActionGardenZ_inRange (ActionGardenZ_inMagnitude core) twoTo64) /\ ((((ActionGardenZ_inSign core) = ActionGardenZ_zOne) \/ ((ActionGardenZ_inSign core) = (ActionGardenZ_baseNeg ActionGardenZ_zOne))) /\ ((ActionGardenZ_inRange (ActionGardenZ_inLeaf core) twoTo255) /\ (forall element : ((ActionGardenZ_Z * ActionGardenZ_Z) * bool), ((In element (ActionGardenZ_inPath core)) -> (ActionGardenZ_inRange (snd (fst element)) twoTo255))))))))))).

Definition ActionGardenZ_actionValueConstraints (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in (((ActionGardenZ_baseSub (ActionGardenZ_inVOld core) (ActionGardenZ_inVNew core)) = (ActionGardenZ_baseMul (ActionGardenZ_inMagnitude core) (ActionGardenZ_inSign core))) /\ (((ActionGardenZ_baseMul (ActionGardenZ_inVOld core) (ActionGardenZ_baseSub ActionGardenZ_zOne (ActionGardenZ_fullEnableSpend input))) = ActionGardenZ_zZero) /\ (((ActionGardenZ_baseMul (ActionGardenZ_inVNew core) (ActionGardenZ_baseSub ActionGardenZ_zOne (ActionGardenZ_fullEnableOutput input))) = ActionGardenZ_zZero) /\ ((not ((ActionGardenZ_fullDisableCrossAddress input) = ActionGardenZ_zZero)) -> (((ActionGardenZ_inGdOld core) = (ActionGardenZ_inGdNew core)) /\ ((ActionGardenZ_inPkdOld core) = (ActionGardenZ_inPkdNew core)))))))).

Definition ActionGardenZ_actionOwnershipValid (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in (let ivkWords := (ActionGardenZ_commitIvkMessageGarden (ActionGardenZ_extractXGarden (ActionGardenZ_inAk core)) (ActionGardenZ_inNk core)) in (let oldNoteWords := (ActionGardenZ_noteCommitMessageGarden (ActionGardenZ_inGdOld core) (ActionGardenZ_inPkdOld core) (ActionGardenZ_inVOld core) (ActionGardenZ_inRhoOld core) (ActionGardenZ_inPsiOld core)) in (let ivkPoint := (ActionGardenZ_commitIvk parameters (ActionGardenZ_extractXGarden (ActionGardenZ_inAk core)) (ActionGardenZ_inNk core) (ActionGardenZ_inRivk core)) in ((ActionGardenZ_sinsemillaHashDefinedGarden (ActionGardenZ_paramsCommitIvkQ parameters) ivkWords) /\ (((ActionGardenZ_inPkdOld core) = (ActionGardenZ_scalarMul (ActionGardenZ_extractXGarden ivkPoint) (ActionGardenZ_inGdOld core))) /\ ((ActionGardenZ_sinsemillaHashDefinedGarden (ActionGardenZ_paramsNoteCommitQ parameters) oldNoteWords) /\ ((ActionGardenZ_inCmOld core) = (ActionGardenZ_noteCommit parameters (ActionGardenZ_inGdOld core) (ActionGardenZ_inPkdOld core) (ActionGardenZ_inVOld core) (ActionGardenZ_inRhoOld core) (ActionGardenZ_inPsiOld core) (ActionGardenZ_fullRcmOld input)))))))))).

Definition ActionGardenZ_actionMerkleValid (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in (((List.length (ActionGardenZ_inPath core)) = 32%nat) /\ ((ActionGardenZ_pathLayersCanonical (ActionGardenZ_inPath core)) /\ ((ActionGardenZ_merklePathDefinedGarden (ActionGardenZ_paramsMerkleCrhQ parameters) (ActionGardenZ_inLeaf core) (ActionGardenZ_inPath core)) /\ (((ActionGardenZ_inLeaf core) = (ActionGardenZ_extractXGarden (ActionGardenZ_inCmOld core))) /\ (((ActionGardenZ_inVOld core) = ActionGardenZ_zZero) \/ ((ActionGardenZ_inAnchorPublic core) = (ActionGardenZ_merkleRootGarden (ActionGardenZ_paramsMerkleCrhQ parameters) (ActionGardenZ_inLeaf core) (ActionGardenZ_inPath core))))))))).

Definition ActionGardenZ_actionNewNoteValid (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  (let core := (ActionGardenZ_fullAction input) in (let nfOld := (ActionGardenZ_nullifier (ActionGardenZ_inNk core) (ActionGardenZ_inRhoOld core) (ActionGardenZ_inPsiOld core) (ActionGardenZ_inCmOld core)) in (ActionGardenZ_sinsemillaHashDefinedGarden (ActionGardenZ_paramsNoteCommitQ parameters) (ActionGardenZ_noteCommitMessageGarden (ActionGardenZ_inGdNew core) (ActionGardenZ_inPkdNew core) (ActionGardenZ_inVNew core) nfOld (ActionGardenZ_inPsiNew core))))).

Definition ActionGardenZ_validActionInputs (parameters : ActionGardenZ_Params) (input : ActionGardenZ_FullActionInputs) : Prop :=
  ((ActionGardenZ_actionParametersValid parameters) /\ ((ActionGardenZ_actionInputsTyped input) /\ ((ActionGardenZ_actionRangesValid input) /\ ((ActionGardenZ_actionValueConstraints input) /\ ((ActionGardenZ_actionOwnershipValid parameters input) /\ ((ActionGardenZ_actionMerkleValid parameters input) /\ (ActionGardenZ_actionNewNoteValid parameters input))))))).

Definition ActionGardenZ_orchardAction (parameters : ActionGardenZ_Params) (input : ActionGardenZ_ActionInputs) : ActionGardenZ_ActionOutputs :=
  (let nfOld := (ActionGardenZ_nullifier (ActionGardenZ_inNk input) (ActionGardenZ_inRhoOld input) (ActionGardenZ_inPsiOld input) (ActionGardenZ_inCmOld input)) in {| ActionGardenZ_outAnchor := (if (ActionGardenZ_zEq (ActionGardenZ_inVOld input) ActionGardenZ_zZero) then (ActionGardenZ_inAnchorPublic input) else (ActionGardenZ_merkleRootGarden (ActionGardenZ_paramsMerkleCrhQ parameters) (ActionGardenZ_inLeaf input) (ActionGardenZ_inPath input))); ActionGardenZ_outCvNet := (ActionGardenZ_valueCommit (ActionGardenZ_signedNetValue (ActionGardenZ_inMagnitude input) (ActionGardenZ_inSign input)) (ActionGardenZ_inRcv input)); ActionGardenZ_outNfOld := nfOld; ActionGardenZ_outRk := (ActionGardenZ_spendAuthRandomize (ActionGardenZ_inAk input) (ActionGardenZ_inAlpha input)); ActionGardenZ_outCmx := (ActionGardenZ_extractXGarden (ActionGardenZ_noteCommit parameters (ActionGardenZ_inGdNew input) (ActionGardenZ_inPkdNew input) (ActionGardenZ_inVNew input) nfOld (ActionGardenZ_inPsiNew input) (ActionGardenZ_inRcmNew input))) |}).
