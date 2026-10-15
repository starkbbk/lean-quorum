import LeanQuorum.Certificates
import LeanQuorum.Checker

/-!
# Kernel-checked boundary examples

These examples encode the actual signer sets and votes. In particular, the
first counterexample contains two conflicting certificates while every honest
validator obeys the no-double-vote rule.
-/

namespace LeanQuorum.Counterexamples

def committee : Finset ℕ := {0, 1, 2}
def faulty : Finset ℕ := {0}
def leftSigners : Finset ℕ := {0, 1}
def rightSigners : Finset ℕ := {0, 2}

def votes (v : ℕ) (value : Bool) : Prop :=
  if value then v ∈ rightSigners else v ∈ leftSigners

theorem honest_votes : HonestVotes faulty votes := by
  intro v hv a b ha hb
  cases a <;> cases b <;> simp_all [votes, faulty, leftSigners, rightSigners]

def leftCertificate : Certificate committee 2 votes false where
  signers := leftSigners
  quorum := by decide
  supports := by intro v hv; exact hv

def rightCertificate : Certificate committee 2 votes true where
  signers := rightSigners
  quorum := by decide
  supports := by intro v hv; exact hv

/-- Two strict majorities may intersect only at a Byzantine validator. -/
theorem strict_majority_can_be_insufficient :
    committee.card < 2 + 2 ∧ faulty.card = 1 ∧
      leftSigners ∩ rightSigners = faulty := by decide

/-- Replacing the strict safety inequality by a non-strict one is unsound. -/
theorem equality_boundary_is_unsafe :
    committee.card + faulty.card = 2 + 2 ∧
      checkSafety committee 2 faulty = false := by decide

theorem honest_rule_allows_conflicting_certificates :
    HonestVotes faulty votes ∧
      Nonempty (Certificate committee 2 votes false) ∧
      Nonempty (Certificate committee 2 votes true) ∧ (false : Bool) ≠ true :=
  ⟨honest_votes, ⟨leftCertificate⟩, ⟨rightCertificate⟩, by decide⟩

/-- Even with no faults, exactly-half quorums can be disjoint. -/
theorem half_quorums_can_split :
    IsQuorum (Finset.range 4) 2 ({0, 1} : Finset ℕ) ∧
      IsQuorum (Finset.range 4) 2 ({2, 3} : Finset ℕ) ∧
      ({0, 1} : Finset ℕ) ∩ {2, 3} = ∅ := by decide

/-- The standard four-validator, one-fault, three-signature configuration. -/
theorem four_validator_safe : checkSafety (Finset.range 4) 3 {0} = true := by decide

theorem seven_validator_safe : checkSafety (Finset.range 7) 5 {0, 1} = true :=
  checkSafety_of_bound (f := 2) (by decide) (by decide)

/-- Zero thresholds admit the empty signer set and therefore cannot be safe. -/
theorem zero_threshold_is_unsafe : checkSafety (Finset.range 4) 0 ∅ = false := by decide

end LeanQuorum.Counterexamples
