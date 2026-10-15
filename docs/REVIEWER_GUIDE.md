# A reviewer’s guide to Lean Quorum

This is a reproducible Lean 4/Mathlib work sample about quorum safety. The most
useful evidence is the connection between an executable implementation, its
inductive invariant, and the final theorem statements. Development used AI
assistance, as disclosed in the README.

## Start with the implementation and its invariant

Read [`BallotBox.lean`](../LeanQuorum/BallotBox.lean):

1. `NoConflict` checks the actual stored vote pairs for a validator.
2. `submit` accepts a faulty validator's vote, or a non-conflicting honest vote.
3. `submit_preserves_invariant` proves the honest-voting invariant after one step.
4. `process_preserves_invariant` proves the result for arbitrary finite traces
   by induction, including traces that contain adversarial votes.
5. `processed_certificate_agreement` derives agreement of certificates built
   from the resulting state. Its assumptions concern the committee and fault
   budget; honest no-double-voting is established by the implementation proof.
6. `processed_snapshot_agreement` handles certificates before and after a
   trace extension, using both state monotonicity and the invariant.

The collector is an abstract authenticated vote-collection component. It is not
a complete consensus protocol or a signature implementation. The fault set is
an explicit model parameter. Faulty votes are intentionally allowed to conflict.

## Check that the specification says the intended thing

In [`Certificates.lean`](../LeanQuorum/Certificates.lean), a certificate carries
an explicit finite signer set, a membership-and-threshold proof, and evidence
that every signer voted for the claimed value. Values are arbitrary, not just
Booleans. Honest voting is scoped to one fixed instance.

In [`Intersection.lean`](../LeanQuorum/Intersection.lean), confirm that both
signer sets belong to the same committee and that the fault budget is bounded.
The threshold condition is strict. In [`Weighted.lean`](../LeanQuorum/Weighted.lean),
the fault budget bounds voting power, not the number of faulty identities.

## Inspect concrete countermodels to tempting review mistakes

The following are synthetic review exercises with explicit, kernel-checked
models. They are not claimed platform responses or past professional reviews.

| Tempting mistake | What the checked example establishes | Source |
| --- | --- | --- |
| Drop signer membership in the committee | Outsider signer sets meet numeric thresholds yet have no overlap | `ReviewCases.missing_membership_countermodel` |
| Assume intersection alone gives agreement | Safe quorum sets can certify two values when the honest-voting rule is absent | `ReviewCases.missing_honesty_countermodel` |
| Check honesty separately in each snapshot | One identity can change its vote between snapshots unless votes are preserved | `ReviewCases.separate_snapshot_honesty_countermodel` |
| Count raw signatures rather than distinct signers | Three copies of the same signature are one signer | `ReviewCases.duplicate_signature_countermodel` |
| Substitute fault cardinality for faulty voting power | One faulty identity can control seven of ten units of voting power | `ReviewCases.cardinal_fault_budget_is_not_weight_budget` |
| Replace `n + f < 2q` with `n + f ≤ 2q` | At equality, conflicting certificates can share only faulty validators | `Counterexamples.equality_boundary_is_unsafe` |
| Equate ordinary majority with Byzantine safety | Two strict majorities may overlap only at a faulty identity | `Counterexamples.strict_majority_can_be_insufficient` |

The first five are in [`ReviewCases.lean`](../LeanQuorum/ReviewCases.lean); the
last two are in [`Counterexamples.lean`](../LeanQuorum/Counterexamples.lean).

The collector examples also check observable behavior: an honest conflicting
vote is rejected, both conflicting faulty votes remain, and exact repetitions
do not inflate the signer count.

## Reproduce the evidence

```bash
lake exe cache get
python3 scripts/verify.py
```

The script builds the project, inspects transitive axiom dependencies of every
project declaration, runs the exhaustive checker, and verifies that the audit
rejects an injected incomplete theorem, an incomplete definition proof, and a
project-defined axiom. The injections live only in temporary test files.

[`checkSafety_iff`](../LeanQuorum/Checker.lean) connects the executable Boolean
checker to its finite-input specification. The finite regression sweep is
separate from the parametric proof of safety for arbitrary finite committees.

[`Audit.lean`](../Audit.lean) accepts only `propext`, `Classical.choice`, and
`Quot.sound` as foundational axioms. This checks proof dependencies; it does not
establish that the theorem statements are the right model of an external system.

## Suggested follow-up questions

- Which branch of `submit_preserves_invariant` rules out a newly inserted
  honest vote conflicting with an old vote?
- Why is honesty of the final combined vote relation needed for agreement
  across snapshots?
- Why does the weighted proof still work when some validators have zero power?
- What exactly does `safe_available_iff` prove, and why is it not a general
  distributed-consensus impossibility result?
- Which authenticated-identity and network properties remain outside the model?
