Require Export Coq.ZArith.ZArith.
Require Export List.
Import ListNotations.
Require Export AirStructure.
Open Scope Z_scope.


Module Blake3AIR (F : PrimeField).

  Module AIRInstance := AirStructure.AIR(F).
  Import AIRInstance.
  
  
  (* Blake3 constants *)
  Definition BITS_PER_LIMB := 16.
  Definition U32_LIMBS := 2.

  (* IV constants for Blake3 *)
  Definition IV : list (list Z) :=
    [
      [0xE667; 0x6A09];
      [0xAE85; 0xBB67];
      [0xF372; 0x3C6E];
      [0xF53A; 0xA54F];
      [0x527F; 0x510E];
      [0x688C; 0x9B05];
      [0xD9AB; 0x1F83];
      [0xCD19; 0x5BE0]
    ].

  

  (* Implementation of add2 as in the Rust code *)
  Definition add2 (builder : AirBuilder) (a : list Var) (b : list Var) (c : list Expr) : AirBuilder :=
    match a, b, c with
    | [a0; a1], [b0; b1], [c0; c1] =>
      (* By assumption p > 2^17 so 1 << 16 will be less than p *)
      let two_16 := Const (2^16) in
      let two_32 := Const (2^32) in

      (* conversion from variable to expression *)
      let a0 := FromVariable a0 in
      let a1 := FromVariable a1 in
      let b0 := FromVariable b0 in
      let b1 := FromVariable b1 in
      
      (* Calculate acc_16 = a[0] - b[0] - c[0] *)
      let acc_16 := Sub a0 (Add b0 c0) in
      
      (* Calculate acc_32 = a[1] - b[1] - c[1] *)
      let acc_32 := Sub a1 (Add b1 c1) in
      
      (* Calculate acc = acc_16 + acc_32 * 2^16 *)
      let shifted_acc_32 := Mul acc_32 two_16 in
      let acc := Add acc_16 shifted_acc_32 in
      
      (* Assert acc * (acc + 2^32) = 0 *)
      let constraint1 := Mul acc (Add acc two_32) in
      
      (* Assert acc_16 * (acc_16 + 2^16) = 0 *)
      let constraint2 := Mul acc_16 (Add acc_16 two_16) in
      
      (* Add both constraints to the builder *)
      let builder := assert_eq builder constraint1 (Const F.zero) in
      let builder := assert_eq builder constraint2 (Const F.zero) in
      
      builder
    | _, _, _ => builder (* Invalid input - should have exactly 2 limbs each *)
    end.

  (* Implementation of add3 as per the Rust signature *)
  Definition add3 (builder : AirBuilder) (a : list Var) (b : list Var) (c : list Expr) (d : list Expr) : AirBuilder :=
    match a, b, c, d with
    | [a0; a1], [b0; b1], [c0; c1], [d0; d1] =>
      (* Similar to add2, but with three addends *)
      let two_16 := Const (2^16) in
      let two_32 := Const (2^32) in
      let double_two_16 := Const (2^17) in
      let double_two_32 := Const (2^33) in
      
      (* Calculate acc_16 = a[0] - b[0] - c[0] - d[0] (assuming d affects only low limb) *)
      let acc_16 := Sub (FromVariable a0) (Add (Add (FromVariable b0) c0) d0) in
      
      (* Calculate acc_32 = a[1] - b[1] - c[1] - d[1] *)
      let acc_32 := Sub (FromVariable a1) (Add (Add (FromVariable b1) c1) d1) in
      
      (* Calculate acc = acc_16 + acc_32 * 2^16 *)
      let shifted_acc_32 := Mul acc_32 two_16 in
      let acc := Add acc_16 shifted_acc_32 in
      
      (* Assert acc * (acc + 2^32) * (acc + 2 * 2^32) = 0 *)
      let constraint1 := Mul (Mul acc (Add acc two_32)) (Add acc double_two_32) in
      
      (* Assert acc_16 * (acc_16 + 2^16) * (acc_16 + 2 * 2^16) = 0 *)
      let constraint2 := Mul (Mul acc_16 (Add acc_16 two_16)) (Add acc_16 double_two_16) in
      
      (* Add both constraints to the builder *)
      let builder := assert_eq builder constraint1 (Const F.zero) in
      let builder := assert_eq builder constraint2 (Const F.zero) in
      
      builder
    | _, _, _, _ => builder (* Invalid input *)
    end.

  Definition xor_32_shift (builder : AirBuilder) (a b c : list Var) (shift : nat) : AirBuilder :=
    match a, length b, length c with
    | [a0; a1], 32%nat, 32%nat =>
        let builder := fold_left (fun builder' var => assert_bool builder' (FromVariable var)) c builder in

      builder
    | _, _, _ => builder (* Invalid input - should have exactly 2 limbs each *)
    end.

End Blake3AIR.