import LeanQuorum.BallotBox
import LeanQuorum.Counterexamples
import LeanQuorum.Weighted

/-!
# Synthetic formalization-review cases

Each case encodes a concrete defect in a tempting weakened claim. These are
self-contained examples, not reviews of platform submissions. A proof compiling
does not establish that its statement captures the intended specification.
-/

namespace LeanQuorum.ReviewCases

/-- Dropping committee membership permits unrelated outsider signer sets. -/
theorem missing_membership_countermodel :
    ∃ committee left right : Finset ℕ,
      left.card ≥ 2 ∧ right.card ≥ 2 ∧ committee.card < 2 + 2 ∧
      left ∩ right = ∅ := by
  exact ⟨∅, {0, 1}, {2, 3}, by decide⟩

def unrestrictedVotes (_ : ℕ) (_ : Bool) : Prop := True

def unrestrictedCertificate (value : Bool) :
    Certificate (Finset.range 4) 3 unrestrictedVotes value where
  signers := Finset.range 4
  quorum := by decide
  supports := by intro _ _; trivial

/-- Correct quorum intersection alone does not imply agreement of voted values. -/
theorem missing_honesty_countermodel :
    checkSafety (Finset.range 4) 3 ∅ = true ∧
      Nonempty (Certificate (Finset.range 4) 3 unrestrictedVotes false) ∧
      Nonempty (Certificate (Finset.range 4) 3 unrestrictedVotes true) ∧
      ¬ HonestVotes ∅ unrestrictedVotes := by
  refine ⟨by decide, ⟨unrestrictedCertificate false⟩,
    ⟨unrestrictedCertificate true⟩, ?_⟩
  intro h
  have hfalse := h 0 (by simp) false true trivial trivial
  cases hfalse

def earlierVotes (validator : ℕ) (value : Bool) : Prop := validator = 0 ∧ value = false
def laterVotes (validator : ℕ) (value : Bool) : Prop := validator = 0 ∧ value = true

theorem earlier_honesty : HonestVotes ∅ earlierVotes := by
  intro _ _ _ _ ha hb
  exact ha.2.trans hb.2.symm

theorem later_honesty : HonestVotes ∅ laterVotes := by
  intro _ _ _ _ ha hb
  exact ha.2.trans hb.2.symm

def earlierCertificate : Certificate {0} 1 earlierVotes false where
  signers := {0}
  quorum := by decide
  supports := by intro v hv; exact ⟨Finset.mem_singleton.mp hv, rfl⟩

def laterCertificate : Certificate {0} 1 laterVotes true where
  signers := {0}
  quorum := by decide
  supports := by intro v hv; exact ⟨Finset.mem_singleton.mp hv, rfl⟩

/-- Each snapshot is internally honest and has a valid certificate. Without
vote preservation, those two certificates can still disagree. -/
theorem separate_snapshot_honesty_countermodel :
    HonestVotes ∅ earlierVotes ∧ HonestVotes ∅ laterVotes ∧
      Nonempty (Certificate {0} 1 earlierVotes false) ∧
      Nonempty (Certificate {0} 1 laterVotes true) ∧
      ¬ (∀ v value, earlierVotes v value → laterVotes v value) := by
  refine ⟨earlier_honesty, later_honesty, ⟨earlierCertificate⟩, ⟨laterCertificate⟩, ?_⟩
  intro h
  have hbad := (h 0 false ⟨rfl, rfl⟩).2
  cases hbad

/-- Three copies of one signature are one distinct signer, not a quorum of three. -/
theorem duplicate_signature_countermodel :
    ([0, 0, 0] : List ℕ).length = 3 ∧
      ([0, 0, 0] : List ℕ).toFinset.card = 1 ∧
      ¬ IsQuorum (Finset.range 4) 3 ([0, 0, 0] : List ℕ).toFinset := by decide

def concentratedPower (validator : ℕ) : ℕ := if validator = 0 then 7 else 1

/-- One faulty identity can control most voting power. Cardinality fault
budgets cannot be substituted for weighted fault budgets. -/
theorem cardinal_fault_budget_is_not_weight_budget :
    ({0} : Finset ℕ).card = 1 ∧
      weight concentratedPower ({0} : Finset ℕ) = 7 ∧
      weight concentratedPower (Finset.range 4) = 10 ∧
      weight concentratedPower ({0, 1} : Finset ℕ) = 8 ∧
      weight concentratedPower ({0, 2} : Finset ℕ) = 8 ∧
      ({0, 1} : Finset ℕ) ∩ {0, 2} = {0} := by decide

/-- The executable collector rejects an honest conflicting vote while retaining
both votes of a faulty identity, as the intended fault model requires. -/
theorem guarded_collector_example :
    BallotBox.process ({0} : Finset ℕ) ∅
      [(1, false), (1, true), (0, false), (0, true)] =
      ({(1, false), (0, false), (0, true)} : Finset (ℕ × Bool)) := by decide

theorem collector_deduplicates_repeated_votes :
    (BallotBox.process (∅ : Finset ℕ) ∅ [(1, true), (1, true), (1, true)]).card = 1 :=
  by decide

end LeanQuorum.ReviewCases
