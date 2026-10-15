import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Quorum intersection with an explicit fault set

All sets are finite sets of validator identities, so duplicate signatures never
increase a quorum's cardinality. The committee is explicit: every claimed quorum
must be a subset of the same validator set.
-/

namespace LeanQuorum

variable {Validator : Type*} [DecidableEq Validator]

/-- A quorum consists of at least `q` distinct members of the validator committee. -/
def IsQuorum (committee : Finset Validator) (q : ℕ) (members : Finset Validator) : Prop :=
  members ⊆ committee ∧ q ≤ members.card

instance (committee : Finset Validator) (q : ℕ) (members : Finset Validator) :
    Decidable (IsQuorum committee q members) :=
  inferInstanceAs (Decidable (members ⊆ committee ∧ q ≤ members.card))

omit [DecidableEq Validator] in
theorem IsQuorum.mono_threshold {committee members : Finset Validator} {q r : ℕ}
    (h : IsQuorum committee q members) (hr : r ≤ q) : IsQuorum committee r members :=
  ⟨h.1, hr.trans h.2⟩

omit [DecidableEq Validator] in
theorem IsQuorum.threshold_le_universe {committee members : Finset Validator} {q : ℕ}
    (h : IsQuorum committee q members) : q ≤ committee.card :=
  h.2.trans (Finset.card_le_card h.1)

/-- Inclusion-exclusion gives a lower bound without truncated subtraction. -/
theorem intersection_card_bound {committee left right : Finset Validator}
    (hl : left ⊆ committee) (hr : right ⊆ committee) :
    left.card + right.card ≤ committee.card + (left ∩ right).card := by
  have hu := Finset.card_le_card (Finset.union_subset hl hr)
  have hi := Finset.card_union_add_card_inter left right
  omega

/-- At most `faulty.card` members of an overlap can be faulty. -/
theorem honest_intersection_card_bound {committee left right : Finset Validator}
    (faulty : Finset Validator) (hl : left ⊆ committee) (hr : right ⊆ committee) :
    left.card + right.card ≤
      committee.card + faulty.card + ((left ∩ right) \ faulty).card := by
  have hi := intersection_card_bound hl hr
  have hs := Finset.card_sdiff_add_card_inter (left ∩ right) faulty
  have hf := Finset.card_le_card (Finset.inter_subset_right :
    (left ∩ right) ∩ faulty ⊆ faulty)
  omega

/-- Different read/write thresholds are allowed. -/
theorem quorum_honest_card_bound {committee left right : Finset Validator}
    {qLeft qRight f : ℕ} (faulty : Finset Validator)
    (hl : IsQuorum committee qLeft left) (hr : IsQuorum committee qRight right)
    (hf : faulty.card ≤ f) :
    qLeft + qRight ≤ committee.card + f + ((left ∩ right) \ faulty).card := by
  have hi := honest_intersection_card_bound faulty hl.1 hr.1
  have hql := hl.2
  have hqr := hr.2
  omega

/-- If the two thresholds beat the committee plus the fault budget, some shared
validator is honest. No assumption that faults are inside the committee is needed. -/
theorem exists_honest_intersection {committee left right : Finset Validator}
    {qLeft qRight f : ℕ} (faulty : Finset Validator)
    (hl : IsQuorum committee qLeft left) (hr : IsQuorum committee qRight right)
    (hf : faulty.card ≤ f) (hsafe : committee.card + f < qLeft + qRight) :
    ∃ v, v ∈ left ∧ v ∈ right ∧ v ∉ faulty := by
  have hcard := quorum_honest_card_bound faulty hl hr hf
  have hpos : 0 < ((left ∩ right) \ faulty).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_sdiff.mp hv with ⟨hboth, hhonest⟩
  exact ⟨v, (Finset.mem_inter.mp hboth).1, (Finset.mem_inter.mp hboth).2, hhonest⟩

/-- Ordinary strict majorities intersect when there are no faulty validators. -/
theorem majority_intersection {committee left right : Finset Validator} {q : ℕ}
    (hl : IsQuorum committee q left) (hr : IsQuorum committee q right)
    (hmajority : committee.card < q + q) : ∃ v, v ∈ left ∧ v ∈ right := by
  obtain ⟨v, hvl, hvr, _⟩ := exists_honest_intersection (f := 0) ∅ hl hr (by simp)
    (by simpa using hmajority)
  exact ⟨v, hvl, hvr⟩

/-- With `3f + 1` validators, two `2f + 1` quorums share an honest validator. -/
theorem bft_intersection {committee left right : Finset Validator} {f : ℕ}
    (faulty : Finset Validator) (hn : committee.card = 3 * f + 1)
    (hl : IsQuorum committee (2 * f + 1) left)
    (hr : IsQuorum committee (2 * f + 1) right) (hf : faulty.card ≤ f) :
    ∃ v, v ∈ left ∧ v ∈ right ∧ v ∉ faulty :=
  exists_honest_intersection faulty hl hr hf (by omega)

/-- Removing all faulty validators leaves enough distinct signers whenever
`q + f ≤ n`. This establishes quorum availability at the set level. -/
theorem honest_quorum_available {committee : Finset Validator} {q f : ℕ}
    (faulty : Finset Validator) (hf : faulty.card ≤ f)
    (ha : q + f ≤ committee.card) :
    IsQuorum committee q (committee \ faulty) := by
  have hcard := Finset.card_le_card_sdiff_add_card (s := committee) (t := faulty)
  exact ⟨Finset.sdiff_subset, by omega⟩

end LeanQuorum
