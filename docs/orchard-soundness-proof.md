# The Orchard Action-statement theorem: statement, assumptions, and scope

Orchard is Zcash's shielded payment protocol. Funds live in private
*notes*; each *action* in a transaction simultaneously spends one note and
creates one, revealing neither values nor addresses. What an action makes
public is only: an *anchor* (a Merkle root committing to the set of
existing notes), the spent note's *nullifier* (preventing double spends),
a *net value commitment* (hiding the value moved while allowing the
transaction to balance), a randomized *spend-authorization key* `rk`, the
new note's *commitment* `cmx`, and two enable flags. A zero-knowledge
proof certifies that these public values are consistent with some hidden
witness — that the spent note exists under the anchor, that the spender
owns it, that the nullifier and commitments are computed correctly. The
required conditions are the protocol's *Action statement* (§4.18.4 of the
Zcash protocol specification), and the circuit whose satisfiability the
proof attests is its deployed Halo 2 implementation.

This document describes the machine-checked theorem that the circuit
**soundly enforces the Action statement**: every assignment the circuit
accepts satisfies it. It gives the exact statements, each hypothesis and
why it is there, the corollaries — determinism per action, value balance
per transaction — and the boundaries of the claim. ("Soundness" here is
statement-level soundness of the constraint system against the
specification; cryptographic soundness of the proving system is a
non-claim, listed below.)

## The theorem

The main theorem lives in `Garden/Orchard/circuit_proof/main.v` (module
`OrchardAction`):

```
Theorem action_statement
    (Γ : Assignment.t columns RegionId.t) (Hcircuit : Holds Γ)
    (Hmerkle_ok : OrchardActionMerkle.merkle_witness_ok Γ)
    (Hnote_ok : NoteCommitNewCmx.note_commit_witness_ok Γ)
    (Hold_note_ok : OrchardValidActionInputs.old_note_witness_ok Γ)
    (Hivk_ok : OrchardValidActionInputs.commit_ivk_witness_ok Γ) :
  (read_action_outputs Γ =
   OrchardProtocolSpec.orchard_action_spec orchard_circuit_params
     (read_action_inputs Γ)) /\
  OrchardValidActionInputs.ValidActionInputs Γ.
```

For any assignment `Γ` that the whole Orchard action circuit accepts
(`Holds Γ`), two things hold.

**The output half** (available standalone as `satisfies_specification`):
the seven public output rows — the anchor, the two coordinates of the net
value commitment, the nullifier, the two coordinates of `rk`, and `cmx` —
equal the specification functions applied to the genuine inputs read from
the assignment. Concretely: the nullifier is the specified function of the
spent note's data; the value commitment commits to exactly
`v_old − v_new`; `rk` is `[α]·SpendAuthG + ak`; `cmx` commits to the new
note; and the anchor is the Merkle root computed from the spent note's
path — except on a *dummy spend* (`v_old = 0`), where the circuit imposes
no Merkle condition and the anchor is the public row itself, mirroring the
gate `v_old · (root − anchor) = 0`. Every fixed-base scalar multiplication
in the specification (`OrchardProtocolSpec`,
`Garden/Orchard/protocol_spec.v`) is a group multiple `Pallas.mul k G` of
the real-coordinate Zcash generator points, and each definition carries
its protocol `§` citation, so the specification is auditable directly
against the protocol.

**The input half** (`ValidActionInputs`,
`circuit_proof/valid_action_inputs.v`): the witnessed inputs satisfy the
Action statement's conditions on the witness itself — the note values are
64-bit integers, the value-balance identity ties them to the
magnitude/sign pair that feeds the value commitment, a nonzero spend or
output requires its enable flag, the spent note's fields open its
commitment `cm_old`, and the spent note's address belongs to the spender
(`pk_d = [ivk]·g_d` with `ivk` derived from the spending authority). The
ownership clause needs the witnessed diversified base to have group order
`q`; this is proved for every on-curve Pallas point
(`PallasOrder.pallas_mul_q_on_curve`,
`Garden/EllipticCurve/PallasOrder.v`, by a Hasse-free counting argument)
and derived for the witnessed base from circuit satisfaction.

**Determinism corollary — `deterministic`.** Two accepted assignments that
agree on the genuine inputs agree on all seven public output rows: each
side equals the specification of the same inputs. Once an action's inputs
are fixed, the circuit admits exactly one value for each public output —
the instance is non-malleable.

`read_action_inputs` (`circuit_proof/inputs.v`) defines what "the genuine
inputs" means, and with it the trust surface of the statement: the
witnessed points and field elements of the two notes, the three windowed
scalars, the magnitude/sign pair, the 32-layer Merkle path, and the public
anchor row. It excludes the square-root witnesses of the fixed-base
ladders: those are free choices of the prover, and the witness-elimination
theorem (`action_spec_us_free`) proves the outputs do not depend on them.

## The hypotheses

**`Hcircuit : Holds Γ`.** Notation for `circuit_holds Γ synthesize
(run configure)`: the assignment satisfies, at every row of every region
produced by the circuit's own synthesis program, all configured gates, the
copy constraints, the constant bindings, and the lookup arguments in their
`Prop` value model. This is the "the circuit accepted the assignment"
premise.

**The four witness-honesty conditions.** All four assert the same two
kinds of per-assignment fact about the witnessed cells: canonical (non-wrapped)
message-piece decompositions, and nondegeneracy of the Sinsemilla and
variable-base-multiplication incomplete additions along their folds. Both
hold for every honestly produced witness, but the gates alone do not force
them in the relational model: the decomposition bounds are enforced in
real Halo2 by short-lookup rows that constrain values only where the
`q_running` selector is zero, and the relational selector model leaves
that selector free at exactly those rows; the incomplete-add gates are, by
design, unconstraining on their exceptional cases. Without the hypotheses
the ANCHOR and CMX outputs would be refutable; naming them keeps this
model gap visible in the statement. They are the exact residue of the
selector idealization listed under the model caveats.

**Input typing.** The range envelope under which the circuit-structured
and protocol layers coincide (full-width scalars in `[0, 8⁸⁵)`, magnitude
in `[0, 8²²)`, a genuine sign bit) is enforced by the circuit:
`protocol_typed_inputs_of_holds` derives it from `Holds Γ` alone. The
theorem therefore carries exactly `Hcircuit` plus the four witness-honesty
conditions.

## Corollary: transaction-level balance

Because every accepted action provably commits to exactly
`v_old − v_new`, the per-action facts compose into the protocol's balance
argument, proved in `Garden/Orchard/bundle/`:
`OrchardBundle.balanced_or_dlog` shows that a bundle of accepted actions
with a valid binding-signature opening either conserves value over ℤ or
exhibits an explicit discrete-log relation between the value-commit
generators, and `no_inflation` extends this to the shielded pool. See
`docs/orchard-balance-proof.md`.

## Constants provenance

The specification's root constants — the Poseidon parameters, the six
fixed-base generators, the Sinsemilla domain points, and the 1024-entry
S table — are each derived in-model from the protocol's algorithms (the
Grain LFSR for Poseidon; the BLAKE2b/SSWU/isogeny hash-to-curve pipeline
for the points, in `Garden/GroupHash/`) and equated with the hard-coded
literal by a `Qed` checker. The vendored reference crates are
version-pinned in `docs/halo2-translation.md`, which also records the
small residue of external trust (the Poseidon reference-implementation
ceiling and the spec-anchored pipeline coefficients).

## What this effort does *not* ensure

- **Crypto soundness.** No theorem here connects the specification to
  cryptographic security properties (collision resistance of
  Sinsemilla/Poseidon, hiding/binding of the commitments, signature
  unforgeability). The claim is that the circuit computes the specified
  functions of its witnessed inputs; the security of the protocol built on
  those functions is a separate question, and the balance corollary names
  its two computational boundaries explicitly.
- **Satisfiability of the witness-honesty hypotheses.** The completeness
  direction (`docs/orchard-completeness-proof.md`) exhibits an accepted
  assignment for every valid, non-degenerate input, so `Holds` is not
  vacuous. It does not discharge the four witness-honesty premises at that
  assignment: the honest generator's non-degeneracy clauses are shaped to
  imply them, but the implications are not proved, so the non-vacuity
  argument for these four hypotheses specifically remains meta-level.
- **Proving-system soundness.** That a verifier accepting a Halo 2 proof
  implies the existence of a satisfying assignment is a property of the
  proving system, not of the circuit, and is not claimed here.

`Holds` is the *relational* interpreter's satisfaction predicate. It is
related to the faithful operational lowering of synthesis (`serialize.v`, the
raw event grid) by the bridge of `docs/operational-soundness.md`, in both
directions at the whole Orchard circuit: `orchard_operational_sound` carries
acceptance by the ideal `mock_prover_accepts` checker back to `Holds`, and
`orchard_operational_complete` carries an honest witness forward to it. The
residual idealization is in the checker itself — it quantifies over all
integer rows rather than the `2^k` cyclic domain.

## Model caveats inherited by the theorems

The relational circuit model (`Garden/Halo2/proof.v`) idealizes real Halo2
in ways documented in `docs/chip-model-caveats.md`; the ones that bear on
how to read these theorems:

- **Regions are independent integer address spaces.** The floor planner is
  abstracted away: gates evaluate at abstract `(region, offset)` pairs, so
  region overlap or a rotation escaping its region cannot be expressed.
  This matches Halo2's usage discipline but is assumed by the model rather
  than proved of the planner.
- **The cyclic evaluation domain and blinding rows are dropped.** Gates
  are quantified over the region's rows in ℤ rather than the wrap-around
  domain. This makes the model slightly more permissive than reality
  (never less).
- **Selector freedom at inactive rows.** Where real Halo2 fixes a selector
  column globally, the model constrains it only at rows the synthesis
  program touches. The `q_running` freedom behind the witness-honesty
  hypotheses is the one place this surfaces in the final statements.
- **Lookup model.** Lookups assert membership in the loaded table with a
  bounded witness row; the table loading and the bound are part of the
  model.

Within those boundaries the per-chip proofs (ECC ladders and
complete/incomplete addition, Sinsemilla hash and Merkle path, Poseidon
permutation, running-sum decompositions, note-commit canonicity) are
derived from the gates without further assumptions.

## Assumption audit

`Print Assumptions` on every theorem named in this document, run against a
full `.vo` build, reports exactly `PrimString.string` (a primitive-string
artifact of the string-keyed column maps) plus the impredicative `Set` the
development is compiled with; the curve-order theorem and the
constants-provenance checkers report no axioms at all. The Pallas
primality facts are `Qed` via Coqprime Pocklington certificates
(`Garden/Field/Primality.v`). No domain-specific or classical axiom
appears on any path.
