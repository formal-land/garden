(* Generated by Garden *)
Require Import Garden.Garden.

(* Function *)
Definition rrot (x n : F.t) : M.t F.t :=
  M.function_body [("x", x); ("n", n)] (
    do~ M.return_ [[ InfixOp.bitAnd ~(| InfixOp.bitOr ~(| InfixOp.shiftR ~(| M.var (| "x" |), M.var (| "n" |) |), InfixOp.shiftL ~(| M.var (| "x" |), InfixOp.sub ~(| 32, M.var (| "n" |) |) |) |), 4294967295 |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition bsigma0 (x : F.t) : M.t F.t :=
  M.function_body [("x", x)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitXor ~(| M.call_function ~(| "rrot", [ M.var (| "x" |); 2 ] |), M.call_function ~(| "rrot", [ M.var (| "x" |); 13 ] |) |), M.call_function ~(| "rrot", [ M.var (| "x" |); 22 ] |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition bsigma1 (x : F.t) : M.t F.t :=
  M.function_body [("x", x)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitXor ~(| M.call_function ~(| "rrot", [ M.var (| "x" |); 6 ] |), M.call_function ~(| "rrot", [ M.var (| "x" |); 11 ] |) |), M.call_function ~(| "rrot", [ M.var (| "x" |); 25 ] |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition ssigma0 (x : F.t) : M.t F.t :=
  M.function_body [("x", x)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitXor ~(| M.call_function ~(| "rrot", [ M.var (| "x" |); 7 ] |), M.call_function ~(| "rrot", [ M.var (| "x" |); 18 ] |) |), InfixOp.shiftR ~(| M.var (| "x" |), 3 |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition ssigma1 (x : F.t) : M.t F.t :=
  M.function_body [("x", x)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitXor ~(| M.call_function ~(| "rrot", [ M.var (| "x" |); 17 ] |), M.call_function ~(| "rrot", [ M.var (| "x" |); 19 ] |) |), InfixOp.shiftR ~(| M.var (| "x" |), 10 |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition Maj (x y z : F.t) : M.t F.t :=
  M.function_body [("x", x); ("y", y); ("z", z)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitXor ~(| InfixOp.bitAnd ~(| M.var (| "x" |), M.var (| "y" |) |), InfixOp.bitAnd ~(| M.var (| "x" |), M.var (| "z" |) |) |), InfixOp.bitAnd ~(| M.var (| "y" |), M.var (| "z" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition Ch (x y z : F.t) : M.t F.t :=
  M.function_body [("x", x); ("y", y); ("z", z)] (
    do~ M.return_ [[ InfixOp.bitXor ~(| InfixOp.bitAnd ~(| M.var (| "x" |), M.var (| "y" |) |), InfixOp.bitAnd ~(| InfixOp.bitXor ~(| 4294967295, M.var (| "x" |) |), M.var (| "z" |) |) |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition sha256K (i : F.t) : M.t F.t :=
  M.function_body [("i", i)] (
    (* Var *)
    do~ M.declare_var "k" [[ [ 64 ] ]] in
    do~ M.substitute_var "k" [[ array_with_repeat (0) (64) ]] in
    do~ M.substitute_var "k" [[ [ 1116352408; 1899447441; 3049323471; 3921009573; 961987163; 1508970993; 2453635748; 2870763221; 3624381080; 310598401; 607225278; 1426881987; 1925078388; 2162078206; 2614888103; 3248222580; 3835390401; 4022224774; 264347078; 604807628; 770255983; 1249150122; 1555081692; 1996064986; 2554220882; 2821834349; 2952996808; 3210313671; 3336571891; 3584528711; 113926993; 338241895; 666307205; 773529912; 1294757372; 1396182291; 1695183700; 1986661051; 2177026350; 2456956037; 2730485921; 2820302411; 3259730800; 3345764771; 3516065817; 3600352804; 4094571909; 275423344; 430227734; 506948616; 659060556; 883997877; 958139571; 1322822218; 1537002063; 1747873779; 1955562222; 2024104815; 2227730452; 2361852424; 2428436474; 2756734187; 3204031479; 3329325298 ] ]] in
    do~ M.return_ [[ M.var_access (| "k", [Access.Array (M.var (| "i" |))] |) ]] in
    M.pure BlockUnit.Tt
  ).

(* Function *)
Definition sha256compression (hin inp : F.t) : M.t F.t :=
  M.function_body [("hin", hin); ("inp", inp)] (
    (* Var *)
    do~ M.declare_var "H" [[ [ 8 ] ]] in
    do~ M.substitute_var "H" [[ array_with_repeat (0) (8) ]] in
    (* Var *)
    do~ M.declare_var "a" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "a" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "b" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "b" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "c" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "c" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "d" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "d" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "e" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "e" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "f" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "f" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "g" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "g" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "h" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "h" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "out" [[ [ 256 ] ]] in
    do~ M.substitute_var "out" [[ array_with_repeat (0) (256) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 8 |) ]] (
      do~ M.substitute_var "H" [[ 0 ]] in
      (* Var *)
      do~ M.declare_var "j" [[ ([] : list F.t) ]] in
      do~ M.substitute_var "j" [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), 32 |) ]] (
        do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (M.var (| "i" |))] |), InfixOp.shiftL ~(| M.var_access (| "hin", [Access.Array (InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 32 |), M.var (| "j" |) |))] |), M.var (| "j" |) |) |) ]] in
        do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "a" [[ M.var_access (| "H", [Access.Array (0)] |) ]] in
    do~ M.substitute_var "b" [[ M.var_access (| "H", [Access.Array (1)] |) ]] in
    do~ M.substitute_var "c" [[ M.var_access (| "H", [Access.Array (2)] |) ]] in
    do~ M.substitute_var "d" [[ M.var_access (| "H", [Access.Array (3)] |) ]] in
    do~ M.substitute_var "e" [[ M.var_access (| "H", [Access.Array (4)] |) ]] in
    do~ M.substitute_var "f" [[ M.var_access (| "H", [Access.Array (5)] |) ]] in
    do~ M.substitute_var "g" [[ M.var_access (| "H", [Access.Array (6)] |) ]] in
    do~ M.substitute_var "h" [[ M.var_access (| "H", [Access.Array (7)] |) ]] in
    (* Var *)
    do~ M.declare_var "w" [[ [ 64 ] ]] in
    do~ M.substitute_var "w" [[ array_with_repeat (0) (64) ]] in
    (* Var *)
    do~ M.declare_var "T1" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "T1" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "T2" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "T2" [[ 0 ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 64 |) ]] (
      do~ M.if_ [[ InfixOp.lesser ~(| M.var (| "i" |), 16 |) ]] (* then *) (
        do~ M.substitute_var "w" [[ 0 ]] in
        (* Var *)
        do~ M.declare_var "j" [[ ([] : list F.t) ]] in
        do~ M.substitute_var "j" [[ 0 ]] in
        do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), 32 |) ]] (
          do~ M.substitute_var "w" [[ InfixOp.add ~(| M.var_access (| "w", [Access.Array (M.var (| "i" |))] |), InfixOp.shiftL ~(| M.var_access (| "inp", [Access.Array (InfixOp.sub ~(| InfixOp.add ~(| InfixOp.mul ~(| M.var (| "i" |), 32 |), 31 |), M.var (| "j" |) |))] |), M.var (| "j" |) |) |) ]] in
          do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
          M.pure BlockUnit.Tt
        ) in
        M.pure BlockUnit.Tt
      ) (* else *) (
        do~ M.substitute_var "w" [[ InfixOp.bitAnd ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.call_function ~(| "ssigma1", [ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 2 |))] |) ] |), M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 7 |))] |) |), M.call_function ~(| "ssigma0", [ M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 15 |))] |) ] |) |), M.var_access (| "w", [Access.Array (InfixOp.sub ~(| M.var (| "i" |), 16 |))] |) |), 4294967295 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "T1" [[ InfixOp.bitAnd ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| InfixOp.add ~(| M.var (| "h" |), M.call_function ~(| "bsigma1", [ M.var (| "e" |) ] |) |), M.call_function ~(| "Ch", [ M.var (| "e" |); M.var (| "f" |); M.var (| "g" |) ] |) |), M.call_function ~(| "sha256K", [ M.var (| "i" |) ] |) |), M.var_access (| "w", [Access.Array (M.var (| "i" |))] |) |), 4294967295 |) ]] in
      do~ M.substitute_var "T2" [[ InfixOp.bitAnd ~(| InfixOp.add ~(| M.call_function ~(| "bsigma0", [ M.var (| "a" |) ] |), M.call_function ~(| "Maj", [ M.var (| "a" |); M.var (| "b" |); M.var (| "c" |) ] |) |), 4294967295 |) ]] in
      do~ M.substitute_var "h" [[ M.var (| "g" |) ]] in
      do~ M.substitute_var "g" [[ M.var (| "f" |) ]] in
      do~ M.substitute_var "f" [[ M.var (| "e" |) ]] in
      do~ M.substitute_var "e" [[ InfixOp.bitAnd ~(| InfixOp.add ~(| M.var (| "d" |), M.var (| "T1" |) |), 4294967295 |) ]] in
      do~ M.substitute_var "d" [[ M.var (| "c" |) ]] in
      do~ M.substitute_var "c" [[ M.var (| "b" |) ]] in
      do~ M.substitute_var "b" [[ M.var (| "a" |) ]] in
      do~ M.substitute_var "a" [[ InfixOp.bitAnd ~(| InfixOp.add ~(| M.var (| "T1" |), M.var (| "T2" |) |), 4294967295 |) ]] in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (0)] |), M.var (| "a" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (1)] |), M.var (| "b" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (2)] |), M.var (| "c" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (3)] |), M.var (| "d" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (4)] |), M.var (| "e" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (5)] |), M.var (| "f" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (6)] |), M.var (| "g" |) |) ]] in
    do~ M.substitute_var "H" [[ InfixOp.add ~(| M.var_access (| "H", [Access.Array (7)] |), M.var (| "h" |) |) ]] in
    (* Var *)
    do~ M.declare_var "i" [[ ([] : list F.t) ]] in
    do~ M.substitute_var "i" [[ 0 ]] in
    do~ M.while [[ InfixOp.lesser ~(| M.var (| "i" |), 8 |) ]] (
      (* Var *)
      do~ M.declare_var "j" [[ ([] : list F.t) ]] in
      do~ M.substitute_var "j" [[ 0 ]] in
      do~ M.while [[ InfixOp.lesser ~(| M.var (| "j" |), 32 |) ]] (
        do~ M.substitute_var "out" [[ InfixOp.bitAnd ~(| InfixOp.shiftR ~(| M.var_access (| "H", [Access.Array (M.var (| "i" |))] |), M.var (| "j" |) |), 1 |) ]] in
        do~ M.substitute_var "j" [[ InfixOp.add ~(| M.var (| "j" |), 1 |) ]] in
        M.pure BlockUnit.Tt
      ) in
      do~ M.substitute_var "i" [[ InfixOp.add ~(| M.var (| "i" |), 1 |) ]] in
      M.pure BlockUnit.Tt
    ) in
    do~ M.return_ [[ M.var (| "out" |) ]] in
    M.pure BlockUnit.Tt
  ).