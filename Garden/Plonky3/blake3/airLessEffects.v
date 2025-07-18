Require Import Garden.Plonky3.MLessEffects.
Require Import Garden.Plonky3.UtilLessEffects.
Require Import Garden.Plonky3.blake3.columnsLessEffects.
Require Import Garden.Plonky3.blake3.constants.

Definition quarter_round_function {p} `{Prime p} (trace : QuarterRound.t Z Z) : M.t unit :=    
    (*
    let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().copied());
    let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().copied());  
    *)
    let b_bits_low := Array.slice_first trace.(QuarterRound.b) BITS_PER_LIMB in
    let* b_0_16 := pack_bits_le_array b_bits_low in

    let b_bits_high := Array.slice_from trace.(QuarterRound.b) BITS_PER_LIMB in
    let* b_16_32 := pack_bits_le_array b_bits_high in  
    M.Pure tt.