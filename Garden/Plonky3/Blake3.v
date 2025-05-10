Require Import Plonky3.M.

Module Blake3.
  (*
    /// Verify that the quarter round function has been correctly computed.
    ///
    /// We assume that the values in a, b, c, d have all been range checked to be
    /// either boolean (for b, d) or < 2^16 (for a, c). This both range checks all x', x''
    /// and auxiliary variables as well as checking the relevant constraints between
    /// them to conclude that the outputs are correct given the inputs.
    fn quarter_round_function<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>,
    ) {
        // We need to pack some bits together to verify the additions.
        // First we verify a' = a + b + m_{2i} mod 2^32
        let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().copied());
        let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().copied());

        add3(
            builder,
            trace.a_prime,
            trace.a,
            &[b_0_16, b_16_32],
            trace.m_two_i,
        );

        // Next we verify that d' = (a' ^ d) >> 16 which is equivalently:  a' = d ^ (d' << 16)
        // This also range checks d' and a'.
        xor_32_shift(builder, trace.a_prime, trace.d, trace.d_prime, 16);

        // Next we verify c' = c + d' mod 2^32
        let d_prime_0_16 = pack_bits_le(trace.d_prime[..BITS_PER_LIMB].iter().copied());
        let d_prime_16_32 = pack_bits_le(trace.d_prime[BITS_PER_LIMB..].iter().copied());
        add2(
            builder,
            trace.c_prime,
            trace.c,
            &[d_prime_0_16, d_prime_16_32],
        );

        // Next we verify that b' = (c' ^ b) >> 12 which is equivalently: c' = b ^ (b' << 12)
        // This also range checks b' and c'.
        xor_32_shift(builder, trace.c_prime, trace.b, trace.b_prime, 12);

        // Next we verify a'' = a' + b' + m_{2i + 1} mod 2^32
        let b_prime_0_16 = pack_bits_le(trace.b_prime[..BITS_PER_LIMB].iter().copied());
        let b_prime_16_32 = pack_bits_le(trace.b_prime[BITS_PER_LIMB..].iter().copied());

        add3(
            builder,
            trace.a_output,
            trace.a_prime,
            &[b_prime_0_16, b_prime_16_32],
            trace.m_two_i_plus_one,
        );

        // Next we verify that d'' = (a'' ^ d') << 8 which is equivalently: a'' = d' ^ (d'' << 8)
        // This also range checks d'' and a''.

        xor_32_shift(builder, trace.a_output, trace.d_prime, trace.d_output, 8);

        // Next we verify c'' = c' + d'' mod 2^32
        let d_output_0_16 = pack_bits_le(trace.d_output[..BITS_PER_LIMB].iter().copied());
        let d_output_16_32 = pack_bits_le(trace.d_output[BITS_PER_LIMB..].iter().copied());
        add2(
            builder,
            trace.c_output,
            trace.c_prime,
            &[d_output_0_16, d_output_16_32],
        );

        // Finally we verify that b'' = (c'' ^ b') << 7 which is equivalently: c'' = b' ^ (b'' << 7)
        // This also range checks b'' and c''.
        xor_32_shift(builder, trace.c_output, trace.b_prime, trace.b_output, 7);

        // Assuming all checks pass, a'', b'', c'', d'' are the correct values and have all been range checked.
    }
  *)
  
End Blake3.