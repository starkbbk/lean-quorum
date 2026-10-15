import LeanQuorum.Certificates
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted quorum safety

Natural-number voting weights need not be positive. A positive honest overlap
weight still supplies an honest signer, even when some validators have zero
weight. All certificates use the same fixed weight function and committee.
-/

namespace LeanQuorum

variable {Validator Value : Type*} [DecidableEq Validator]

/-- Total voting power of a deduplicated signer set. -/
def weight (power : Validator → ℕ) (members : Finset Validator) : ℕ :=
  ∑ v ∈ members, power v

omit [DecidableEq Validator] in
theorem weight_mono (power : Validator → ℕ) {left right : Finset Validator}
    (h : left ⊆ right) : weight power left ≤ weight power right :=
  Finset.sum_le_sum_of_subset h

omit [DecidableEq Validator] in
@[simp] theorem weight_empty (power : Validator → ℕ) : weight power ∅ = 0 := by
  simp [weight]

omit [DecidableEq Validator] in
@[simp] theorem unit_weight (members : Finset Validator) :
    weight (fun _ => 1) members = members.card := by
  simp [weight]

theorem weight_union_inter (power : Validator → ℕ) (left right : Finset Validator) :
    weight power (left ∪ right) + weight power (left ∩ right) =
      weight power left + weight power right := by
  exact Finset.sum_union_inter

theorem weighted_intersection_bound (power : Validator → ℕ)
    {committee left right : Finset Validator}
    (hl : left ⊆ committee) (hr : right ⊆ committee) :
    weight power left + weight power right ≤
      weight power committee + weight power (left ∩ right) := by
  have hu := weight_mono power (Finset.union_subset hl hr)
  have hi := weight_union_inter power left right
  omega

theorem weighted_honest_intersection_bound (power : Validator → ℕ)
    {committee left right : Finset Validator} (faulty : Finset Validator)
    (hl : left ⊆ committee) (hr : right ⊆ committee) :
    weight power left + weight power right ≤ weight power committee +
      weight power faulty + weight power ((left ∩ right) \ faulty) := by
  have hi := weighted_intersection_bound power hl hr
  have hsplit : weight power ((left ∩ right) \ faulty) +
      weight power ((left ∩ right) ∩ faulty) = weight power (left ∩ right) := by
    simpa only [weight, Finset.sdiff_inter_self_left] using (Finset.sum_sdiff
      (Finset.inter_subset_left : (left ∩ right) ∩ faulty ⊆ left ∩ right)
      (f := power))
  have hf := weight_mono power (Finset.inter_subset_right :
    (left ∩ right) ∩ faulty ⊆ faulty)
  omega

/-- Weighted analogue of the cardinality-based honest-intersection theorem. -/
theorem exists_weighted_honest_intersection (power : Validator → ℕ)
    {committee left right : Finset Validator} {qLeft qRight faultPower : ℕ}
    (faulty : Finset Validator) (hl : left ⊆ committee) (hr : right ⊆ committee)
    (hql : qLeft ≤ weight power left) (hqr : qRight ≤ weight power right)
    (hf : weight power faulty ≤ faultPower)
    (hsafe : weight power committee + faultPower < qLeft + qRight) :
    ∃ v, v ∈ left ∧ v ∈ right ∧ v ∉ faulty := by
  have hi := weighted_honest_intersection_bound power faulty hl hr
  have hne : (left ∩ right) \ faulty ≠ ∅ := by
    intro he
    rw [he, weight_empty] at hi
    omega
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rcases Finset.mem_sdiff.mp hv with ⟨hboth, hhonest⟩
  exact ⟨v, (Finset.mem_inter.mp hboth).1, (Finset.mem_inter.mp hboth).2, hhonest⟩

structure WeightedCertificate (committee : Finset Validator) (power : Validator → ℕ)
    (q : ℕ) (votes : Validator → Value → Prop) (value : Value) where
  signers : Finset Validator
  subset_committee : signers ⊆ committee
  threshold : q ≤ weight power signers
  supports : ∀ v ∈ signers, votes v value

theorem weighted_certificate_agreement {committee : Finset Validator}
    {power : Validator → ℕ} {qLeft qRight faultPower : ℕ}
    {votes : Validator → Value → Prop} {a b : Value} (faulty : Finset Validator)
    (honest : HonestVotes faulty votes) (hf : weight power faulty ≤ faultPower)
    (hsafe : weight power committee + faultPower < qLeft + qRight)
    (left : WeightedCertificate committee power qLeft votes a)
    (right : WeightedCertificate committee power qRight votes b) : a = b := by
  obtain ⟨v, hvl, hvr, hvh⟩ := exists_weighted_honest_intersection power faulty
    left.subset_committee right.subset_committee left.threshold right.threshold hf hsafe
  exact honest v hvh a b (left.supports v hvl) (right.supports v hvr)

end LeanQuorum
