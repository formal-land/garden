# The Orchard-action determinism theorem: statement, assumptions, and scope

This document describes what the whole-circuit determinism result for the
Zcash Orchard action circuit establishes: the exact theorem statements, each
hypothesis and why it is there, what the conclusion means, and what the
verification effort does and does not ensure given the caveats of the
circuit/synthesis model.

## The theorems

Both theorems live in
`Garden/Orchard/circuit_proof/main.v` (module
`OrchardAction`) and are `Qed`, with an assumption audit recorded below.

**Functional form — `satisfies_specification`.** For any assignment `Γ` of
the Orchard action circuit:

```
Theorem satisfies_specification
    (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
    (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
    (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ) :
  read_action_outputs Γ =
    OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
      (read_action_inputs Γ).
```

where `read_action_outputs` packages the seven primary public-instance rows
(`ANCHOR`; `CV_NET`/`RK` as point coordinates; `NF_OLD`; `CMX`). In words:
**the seven public outputs of any satisfying assignment are the value of the
protocol-aligned specification function applied to the genuine inputs read
from that assignment.** The specification
`OrchardProtocolSpec.orchard_action_spec` (`protocol_spec.v`; its
`orchard_circuit_params` argument is the slim `OrchardSpec.Params` record of
the three Sinsemilla domain points) writes each
§4.18.4 output condition with its fixed-base scalar multiplications as group
multiples `Pallas.mul k G` of the six real-coordinate Zcash generator points
(`Orchard/Pallas/Generators.v`): the net value commitment, the old-note
nullifier (scalar reduced mod `q_P`), `rk = [α]SpendAuthG + ak`, the new-note
commitment x-coordinate (`cmx`) over the 1086-bit / 109-word note-commit
message with its two y-parity terms, and the anchor (the computed Merkle root
when `v_old ≠ 0`, the public anchor row itself on a dummy spend — mirroring
the circuit's `v_old · (root − anchor) = 0` gate, which deliberately imposes
no Merkle condition on dummy spends).

Internally the seven per-output bridges (`anchor_correct`,
`cv_net_x_correct`/`cv_net_y_correct`, `nf_old_correct`,
`rk_x_correct`/`rk_y_correct`, `cmx_correct`) land on `action_spec_of Γ`, the
circuit-structured output of module `OrchardCircuitSpec`
(`circuit_proof/internal_spec.v`: the same output conditions with fixed-base
multiplications as folds over the circuit's Lagrange tables, parameterized by
its own `OrchardCircuitSpec.Params` record — the six window tables plus the
protocol `domain` points, instantiated as `orchard_internal_params` in
`circuit_proof/inputs.v`). The square-root-witness elimination
`OrchardActionUsFreeNullifierK.action_spec_us_free`
(`circuit_proof/us_free/nullifier_k.v`) relates that circuit-structured output
to the witness-free form, and the per-base fold-equals-group-multiple bridge
`OrchardProtocolEquiv.output_protocol_eq` (`circuit_proof/protocol_equiv.v`,
backed by `circuit_proof/protocol_mul/`) carries it onto the protocol form —
both composed inside `satisfies_specification`, which closes by record eta
(`outputs_eta`).

**Determinism corollary — `deterministic`.** Two satisfying assignments that
agree on the genuine inputs (`read_action_inputs Γ1 = read_action_inputs Γ2`,
plus the witness-honesty conditions for each) agree on all seven public
output rows. This is the direct consequence of the functional form: each
side equals the protocol specification of the same inputs.

`read_action_inputs` (`circuit_proof/inputs.v`) reads only the *inputs* of an
action — the witnessed points and field elements (`ak`, `nk`, `ρ_old`,
`ψ_old`, `cm_old`, `g_d`, `v_old`, `v_new`, …), the three windowed scalars
(`α`, `rcv`, `rcm_new`) as their 85-window digit decompositions, the
magnitude/sign pair, the 32-layer Merkle path, and the public anchor row. It
deliberately excludes the square-root witnesses of the fixed-base ladders:
those are benign nondeterminism, and the witness-elimination theorem
(`action_spec_us_free`) proves the outputs do not depend on them.

**Composed Action statement — `action_statement`.** The conjunction of
`satisfies_specification` with the input-side half of §4.18.4
(`OrchardValidActionInputs.ValidActionInputs`,
`circuit_proof/valid_action_inputs.v`: input typing, value balance, the two
enable-flag clauses — covering all nine §4.18.4 primary inputs — and the
two ownership clauses). Both ownership clauses are `Qed` by delegation —
old-note commitment integrity to `OldNoteOpen.old_note_commit_integrity`
(`circuit_proof/old_note/open.v`), diversified address integrity to
`DiversifiedAddress.diversified_address_integrity`
(`circuit_proof/ownership/diversified_address.v`) — under the two
witness-honesty predicates `old_note_witness_ok` / `commit_ivk_witness_ok`
(Sinsemilla nondegeneracy + short-lookup range facts; the `commit_ivk` one
also carries the variable-base-mul step nondegeneracy
`VarBaseMul.mul_nondegenerate` and the `g_d_old` base-order fact
`[q] g_d_old = 𝒪`, a curve-cardinality truth outside the formalized
Weierstrass interface). The variable-base mul chain under the address
clause is fully `Qed`: the four segment lemmas of
`circuit_proof/ownership/var_base_mul.v` (`hi_half_correct`,
`lo_half_correct`, `complete_bits_correct`, `overflow_scalar_exact`)
delegate to the leaf files `var_base_incomplete.v`, `var_base_complete.v`
and `var_base_overflow.v`, so its `Print Assumptions` is the same
`PrimString.string`/impredicative-`Set` baseline as
`satisfies_specification` and `deterministic`.

## The hypotheses, one by one

**`Hcircuit : Holds Γ`.** `Holds Γ` is notation for `circuit_holds Γ
synthesize (run configure)`: the assignment satisfies, at every row of every
region produced by the circuit's own synthesis program, all configured gates,
the copy (permutation) constraints, the constant bindings emitted by
`ConstrainConstant`, and the lookup arguments in their `Prop` value model
(each looked-up tuple equals some row of the loaded table, with the witness
row bounded — which is what gives lookups their range-check force). This is
the "the circuit accepted the assignment" premise; everything else is derived
from it, except the two residual conditions below.

**`Hmerkle_ok : merkle_witness_ok Γ`** — for each of the 32 Merkle layers:

- *canonical decomposition*: the witnessed 255-bit Sinsemilla message-piece
  decomposition of the layer's node/sibling data satisfies the strict
  integer bounds (`< pallas_p`) that make it the canonical representative
  rather than a wrapped one;
- *nondegeneracy*: the layer's Sinsemilla hash never hits the incomplete-add
  exceptional case (equal x-coordinates) along its fold.

*Motivation.* Both facts are true of every honestly produced witness, but the
gates alone do not force them in the relational model: the decomposition
bound is enforced in real Halo2 by a lookup-driven running-sum argument whose
short-lookup rows constrain `z_cur` only where the `q_running` selector is
zero, and the relational selector model leaves `q_running` free at exactly
those rows; the incomplete-add gate is (by design of Sinsemilla) simply
unconstraining on the exceptional case. Without the hypothesis the ANCHOR
output is refutable — a malicious prover could witness a wrapped
decomposition. Surfacing the conditions as named hypotheses keeps the theorem
honest about this model gap instead of hiding it.

**`Hnote_ok : note_commit_witness_ok Γ`** — the same two conditions for the
new-note commitment: nondegeneracy of the Sinsemilla fold over the witnessed
109-word note-commit message, and the short-lookup range facts of the message
pieces. *Motivation:* identical to the Merkle case; without it the CMX output
is refutable.

Both predicates are per-assignment, decidable-in-principle statements about
the witnessed cells; they are the exact residue of the two model
idealizations named below, and they are satisfied by every witness the real
prover produces. At the bridge level no other side condition is assumed: the
CV_NET, NF_OLD and RK output bridges are derived from `Holds Γ` alone.

**Input typing — derived from `Holds`, not assumed.** The protocol
input-typing predicate `ProtocolTypedInputs (read_action_inputs Γ)` — the
three full-width scalars (`α`, `rcv`, `rcm_new`) in `[0, 8⁸⁵)`, the value
magnitude in `[0, 8²²)`, and the sign in `{1, −1}` (as field elements) — is
the range envelope under which the circuit-structured and protocol layers
coincide (the per-base fold-equals-group-multiple bridges hold on the folds'
window domains, and the CV_NET sign decode needs a genuine sign bit). It is
*not* a hypothesis of either theorem: every conjunct is enforced by the
circuit on a satisfying assignment, and the `Qed` theorem
`OrchardValidActionInputs.protocol_typed_inputs_of_holds`
(`circuit_proof/valid_action_inputs.v`, backed by the
`circuit_proof/typed_inputs/` slices) derives the predicate from `Holds Γ`
alone — the three full-width scalars from the incomplete-mul running-sum
window ranges, the magnitude from the 22-window short-mul running sum, and
the sign from the short-mul sign-square gate. The theorem statements
therefore carry exactly `Hcircuit` plus the two witness-honesty conditions
above.

## What the conclusion means

- **Determinism / non-malleability of the instance:** once the inputs of an
  action are fixed, the circuit admits exactly one value for each public
  output. In particular the square-root witnesses of the five fixed-base
  scalar multiplications (SpendAuthG, NullifierK, NoteCommitR, ValueCommitR,
  ValueCommitV), which *are* free choices of the prover, provably do not
  influence any output: the per-window quadratic-residue certificates force
  the witnessed window point to the canonical one.
- **Against the protocol specification, not just uniqueness:** the theorem
  is functional (`= orchard_action_spec inputs`), which is strictly stronger
  than pairwise agreement. It pins the outputs to the independently-auditable
  `OrchardProtocolSpec` functions — fixed-base multiplications as group
  multiples of the real-coordinate Zcash generator points — with the
  remaining constants (Sinsemilla domain points and tables, Poseidon
  parameters, the generator coordinates themselves) cross-checked against
  the vendored Rust `orchard` crate sources by `vm_compute` certificates,
  and the constant-binding sites validated against a Rust-generated replay
  table by the standalone gate `circuit_synthesis_constants_check.v`.

## What this effort does *not* ensure

- **Crypto soundness.** `OrchardSpec.output` mirrors the protocol
  specification, but no theorem here connects it to cryptographic security
  properties (collision resistance of Sinsemilla/Poseidon, hiding/binding of
  the commitments, unforgeability of redemption keys). The statement is
  "the circuit computes the specified functions of its witnessed inputs",
  not "the protocol built on it is secure".
- **Completeness.** The theorems say every satisfying assignment maps to the
  spec value; they do not exhibit a satisfying assignment for every input
  (no inhabitation lemma). In particular the two witness-honesty hypotheses
  are not proved satisfiable-under-`Holds` inside Rocq — their non-vacuity
  argument is meta-level (honest witnesses satisfy them by construction).
- **Relational–operational consistency.** `Holds` is the *relational*
  interpreter's satisfaction predicate. The faithful operational lowering of
  synthesis (`serialize.v`, raw event grid) exists, and the two interpreters
  agree on everything audited so far, but no theorem yet relates them.

## Model caveats inherited by the theorems

The relational circuit model (`Garden/Halo2/proof.v`) idealizes real Halo2 in
ways that are documented in `docs/chip-model-caveats.md`; the ones that bear
on how to read these theorems:

- **Regions are independent integer address spaces.** The floor planner is
  abstracted away: gates evaluate at abstract `(region, offset)` pairs, so
  region overlap or a rotation escaping its region cannot be expressed. This
  matches Halo2's usage discipline but is an axiom of the model, not a
  proved property of the planner.
- **The cyclic evaluation domain and blinding rows are dropped.** Gates are
  quantified over the region's rows in ℤ, not over the wrap-around domain.
  This makes the model slightly more permissive than reality (never less).
- **Selector freedom at inactive rows.** Selectors are modeled relationally;
  where real Halo2 fixes a selector column globally, the model constrains it
  only at rows the synthesis program touches. The `q_running` freedom behind
  the two witness-honesty hypotheses is the one place this surfaces in the
  final statement.
- **Lookup model.** Lookups assert membership in the loaded table with a
  bounded witness row — faithful in force, but the table loading and the
  bound are part of the model rather than derived from an operational
  execution.

Within those boundaries the per-chip proofs (ECC ladders and complete/
incomplete addition, Sinsemilla hash and Merkle path, Poseidon permutation,
running-sum decompositions, note-commit canonicity) are derived from the
gates without further assumptions.

## Assumption audit

`Print Assumptions` on both theorems (`satisfies_specification` and
`deterministic`, full `.vo` build — and likewise on the supporting
`protocol_typed_inputs_of_holds`) reports only
`PrimString.string` (a Rocq primitive-string artifact of the string-keyed
column maps) plus the use of impredicative `Set` the development is compiled
with. The Pallas base- and scalar-field primality facts are `Qed` via
Coqprime Pocklington certificates (`Garden/Field/Primality.v`); no
domain-specific axiom remains on the path.

The composed `action_statement` (and, through it,
`OrchardValidActionInputs.valid_action_inputs_of_holds` and
`diversified_address_integrity`) reports the same baseline: the four
variable-base-mul segment lemmas of
`circuit_proof/ownership/var_base_mul.v` — `hi_half_correct`,
`lo_half_correct`, `complete_bits_correct`, `overflow_scalar_exact` — are
`Qed` by delegation to `var_base_incomplete.v`, `var_base_complete.v` and
`var_base_overflow.v`. `old_note_commit_integrity` and the value-clause
companions `CvNetValue.cv_net_value_balance_sound` /
`cv_net_commits_net_value_Z` likewise carry only the
`PrimString.string`/impredicative-`Set` baseline (full-`.vo` `rocq top`
audit, 2026-07-10).
