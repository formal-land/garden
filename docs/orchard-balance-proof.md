# The Orchard balance theorems: statement, assumptions, and scope

Shielded values in Zcash are hidden inside commitments, so a transaction
cannot be balanced by adding amounts. Orchard balances homomorphically
instead. Each action publishes a *net value commitment*
`cv_net = [v_old − v_new]·V + [rcv]·R`, a Pedersen commitment to the value
it moves, blinded by a trapdoor `rcv`; the transaction declares one public
number, `value_balance` (the net flow between the shielded pool and the
transparent world); and the validator recomputes the *binding validating
key* `bvk = Σ cv_net − Commit_0(value_balance)`. If the hidden values sum
to the declared balance, `bvk` is a commitment to zero and hence equals
`[Σ rcv]·R` — and the transaction's *binding signature*, verifiable under
`bvk`, proves the signer knows such an opening. A transaction that minted
value would need a signature under a key whose discrete log nobody knows,
or a second opening of a Pedersen commitment. This is the protocol's
balance argument (§4.14 of the Zcash protocol specification); combined
with the rule that the shielded pool's running balance may never go
negative (§4.17), it is what makes shielded value non-inflatable.

This document describes the machine-checked form of that argument
(`Garden/Orchard/bundle/`, module `OrchardBundle`), built on the
Action-statement theorem (`docs/orchard-soundness-proof.md`) — in
particular on its clause that every accepted action's `cv_net` commits to
exactly `v_old − v_new`.

## The theorems

A *bundle* (`bundle/spec.v`) is a list of per-action circuit assignments
together with the public `value_balance`. The main theorem:

```
Theorem balanced_or_dlog (b : t) (bsk : Z)
    (Hok : actions_ok b)
    (Hside : side_conditions b)
    (Hsig : SignatureKnowledge b bsk) :
  sum_net_values b = value_balance b \/
  exists k : Z, dlog_relation k.
```

For a bundle whose actions were all accepted by the circuit (with the
per-action package `action_ok`), whose
shape respects the consensus rules — at most `2¹⁶ − 1` actions,
`value_balance` in the signed 64-bit range — and for which a
binding-signature opening `bvk = [bsk]·R` is known: **either the hidden
net values sum exactly to the declared balance, over the integers, or an
explicit discrete-log relation `R = [k]·V` between the two value-commit
generators is exhibited**, with `k` computed from the two openings.

The pool-level corollary:

```
Theorem no_inflation (bundles : list t) ... :
  (Forall (fun b => sum_net_values b = value_balance b) bundles /\
    zsum (map sum_net_values bundles) <= 0) \/
  exists k : Z, dlog_relation k.
```

Over any list of bundles satisfying the same hypotheses, under the §4.17
nonnegative-pool consensus rule: either every bundle balances and the
total net withdrawal from the shielded pool is bounded by what was
deposited, or some bundle yields the discrete-log relation. No collection
of transactions can counterfeit shielded value without a discrete-log
break.

## Why a disjunction: binding as a reduction

The classical statement would assume Pedersen binding — "no adversary can
open one commitment to two values" — and conclude balance outright. In
this development that assumption would be *false*: the Pallas group is
cyclic of prime order (`GroupOrder`/`PallasOrder` in
`Garden/EllipticCurve/`), so some `k` with `R = [k]·V` exists, and the
corresponding independence statement (`[a]V + [b]R = 𝒪 → a ≡ b ≡ 0`) is
refutable inside the model. Binding is a computational property: nobody
*knows* `k`.

The theorems therefore prove the reduction: a balance violation produces
the discrete log — `dlog_relation k` with `k = extracted_k …`
(`bundle/binding_reduction.v`), one modular inversion applied to the two
openings. A consumer invokes discrete-log hardness exactly once, to
discard that disjunct. In exchange the development stays axiom-free (see
the audit below).

## The proof, in three steps

1. **Homomorphic collapse** (`bundle/homomorphic_sum.v`). The
   Action-statement value clause gives `cv_net_i = [v_i]·V + [rcv_i]·R`
   with `v_i = v_old_i − v_new_i` over ℤ. Folding the
   scalar-multiplication homomorphism over the bundle collapses the
   recomputed key to a single commitment: `bvk = [v*]·V + [Σ rcv]·R` where
   `v* = Σ v_i − value_balance`.
2. **Two openings** (`bundle/binding_reduction.v`). The signature opening
   says `bvk = [bsk]·R`, a commitment to zero. If `v* ≢ 0 (mod q)`, the
   two openings of the same point yield `[v*]·V = [bsk − Σ rcv]·R`, and
   inverting the nonzero side modulo the prime group order extracts the
   explicit `k` with `R = [k]·V`.
3. **The integer lift** (`bundle/integer_lift.v`). If `v* ≡ 0 (mod q)`,
   the consensus bounds make the congruence an equality: with at most
   `2¹⁶ − 1` actions, each net value below `2⁶⁴` in magnitude, and
   `value_balance` in the signed 64-bit range,
   `|v*| < 2⁸¹ ≪ (q − 1)/2 ≈ 2²⁵³`, so the only multiple of `q` in reach
   is zero and `v* = 0` over ℤ. This step is where the consensus side
   conditions are load-bearing: without the action-count bound, a
   transaction with astronomically many actions could wrap the sum around
   the group order.

## The hypothesis surface

- **`actions_ok`** — each action satisfies the circuit (`Holds Γ`) plus
  the two short-lookup range families that yield the 64-bit `v_old`/`v_new`
  bounds the integer lift needs. Nothing else: the `cv_net` row is one of
  the five ⊥-free outputs, so the package carries neither the Merkle
  package nor any Sinsemilla nondegeneracy. Both families are model
  artifacts of the relational selector plane and are discharged from
  acceptance of the pinned circuit
  (`OrchardAdversarialAction.action_ok_operational`,
  `Garden/Orchard/circuit_adversarial.v`), so an accepted action satisfies
  the package outright.
- **`side_conditions`** — the two consensus rules used by the lift:
  `n ≤ 2¹⁶ − 1` and `value_balance ∈ [−2⁶³, 2⁶³)`. Both are enforced by
  Zcash consensus outside the circuit.
- **`SignatureKnowledge b bsk`** — the semantic content of a valid binding
  signature: knowledge of `bsk` with `bvk = [bsk]·R`. The step from "the
  RedPallas signature verifies" to this knowledge is the signature
  scheme's security (SUF-CMA plus proof of knowledge of the discrete log,
  §5.4.7.2) and stays outside the model as a named boundary — the same
  status as SNARK knowledge soundness, which is what connects `Holds Γ` to
  deployed proofs in the first place.

## What this does *not* ensure

- The two computational boundaries — signature security and discrete-log
  hardness — are where a consumer's cryptographic assumptions enter;
  neither is proved here.
- The per-action layer's non-claims and model caveats
  (`docs/orchard-soundness-proof.md`) are inherited.
- Consensus rules beyond the two side conditions (nullifier freshness,
  anchor validity, fees) are out of scope.

## Assumption audit

`Print Assumptions` on `balanced_or_dlog` and `no_inflation`, against a
full `.vo` build, reports exactly `PrimString.string` plus impredicative
`Set` — the same baseline as the Action-statement theorem, with no
cryptographic and no classical axiom.
