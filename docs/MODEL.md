# Model and proof walkthrough

## 1. Validators and quorums

The validator identity type is arbitrary. A committee and each signer set are
`Finset Validator` values. Using finite sets makes signer identity deduplication
part of the mathematical representation.

`IsQuorum committee q members` contains two obligations:

1. Every signer belongs to the committee.
2. There are at least `q` distinct signers.

The same committee is used for both certificates. Merely meeting a numeric
threshold is insufficient if a certificate may contain arbitrary outsiders.

## 2. Honest overlap

For signer sets `L` and `R` inside a committee `U`, inclusion-exclusion gives:

```text
|L| + |R| = |L ∪ R| + |L ∩ R|
          ≤ |U| + |L ∩ R|
```

Split the intersection into faulty and honest members:

```text
|L| + |R| ≤ |U| + |F| + |(L ∩ R) \ F|
```

When `qLeft + qRight > |U| + f` and `|F| ≤ f`, the final term must be positive.
Lean extracts a concrete member of that nonempty finite set.

`F` need not itself be a subset of `U`: counting outsiders against the fault
budget only makes the sufficient bound more conservative.

## 3. From overlap to agreement

`votes v a` is a relation, allowing a faulty validator to vote for multiple
values. `HonestVotes F votes` requires that any validator outside `F` has at most
one voted value in the modeled instance.

A `Certificate U q votes a` carries its signer set, quorum proof, and proof
that every signer voted for `a`. An honest member of two certificate signer
sets has voted for both values, so the honest-voting assumption proves equality.

The accountability theorem goes in the other direction: if certified values
differ, every shared signer is faulty. Inclusion-exclusion then bounds the
fault count from below.

Snapshot extension is deliberately explicit. An old certificate can be moved
to an enlarged vote relation, but agreement requires honesty of that enlarged
relation. Separate honesty assumptions for separate snapshots do not prevent
an honest identity from changing its vote between them.

## 4. Threshold optimization and availability

The smallest symmetric threshold satisfying `n + f < 2q` is:

```text
minimumSafeThreshold n f = (n + f) / 2 + 1
```

Count-based availability requires `q + f ≤ n`: the remaining honest validators
can meet the threshold without help from faulty ones. The finite-set theorem
`honest_quorum_available` constructs that quorum as `U \ F`.

There is a threshold satisfying both numeric conditions exactly when `3f < n`.
For `n = 3f + 1`, the minimum is `2f + 1`. The statements use natural numbers
and include zero sizes, impossible thresholds, and integer-rounding boundaries.

This arithmetic equivalence is not a general impossibility theorem for all
distributed protocols, and availability of enough signers is not network liveness.

## 5. Weighted votes

Replace cardinality by the sum of a fixed natural-number weight function over
each signer set. Sum monotonicity and weighted inclusion-exclusion give:

```text
weight(L) + weight(R)
  ≤ weight(U) + weight(F) + weight((L ∩ R) \ F)
```

Zero-weight validators are allowed. Positive honest overlap weight implies a
nonempty honest signer set, which is all the agreement proof needs. Setting
every weight to one recovers cardinality (`unit_weight`).

## 6. The executable checker

`checkSafety` decides a finite proposition over the powerset of a supplied
natural-number committee. It enumerates every quorum pair and checks honest
overlap. `checkSafety_iff` proves the Boolean result is equivalent to the
universal finite-input specification; `checkSafety_false_iff` characterizes
rejection by the existence of a bad quorum pair.

The checker is exponential. The demo bounds enumeration to small committees;
the parametric theorems do not have that restriction.

## 7. Audit boundary

`Audit.lean` traverses every declaration in the `LeanQuorum` namespace, rejects
project-defined axioms, and uses Lean's `collectAxioms` to inspect transitive
dependencies of both theorems and definitions. The only allowed foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The audit detects admitted proofs even inside definitions, such as certificate
constructors carrying proof fields. It does not constitute an independent
implementation of Lean's kernel or replace review of the theorem statements.
