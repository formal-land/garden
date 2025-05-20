Require Import Garden.Plonky3.M.

(*

/// Pack a collection of bits into a number.
///
/// Given `vec = [v_0, v_1, ..., v_n]` returns `v_0 + 2v_1 + ... + 2^n v_n`
#[inline]
pub fn pack_bits_le<R, Var, I>(iter: I) -> R
where
    R: PrimeCharacteristicRing,
    Var: Into<R> + Clone,
    I: DoubleEndedIterator<Item = Var>,
{
    iter.rev()
        .map(Into::into)
        .reduce(|acc, elem| acc.double() + elem)
        .unwrap_or(R::ZERO)
}

*)
Definition pack_bits_le (bits : list Z) : M.t Z :=
  let reversed_bits := List.rev bits in
  [[
    fold (|
      0,  (* Start with zero accumulator *)
      reversed_bits,
      fun acc bit => [[
        M.add (| M.mul (| 2, acc |), bit |)  (* acc * 2 + bit *)
      ]]
    |)
  ]].