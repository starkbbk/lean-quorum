import LeanQuorum.Intersection
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Push

/-!
# A reflected, executable safety checker

The checker enumerates *all* pairs of subsets of a supplied finite committee.
Its soundness and completeness theorem connects the returned Boolean to the
same honest-intersection proposition used by the general safety proofs.
-/

namespace LeanQuorum

def checkSafety (committee : Finset ℕ) (q : ℕ) (faulty : Finset ℕ) : Bool :=
  decide (∀ left ∈ committee.powerset, ∀ right ∈ committee.powerset,
    q ≤ left.card → q ≤ right.card → ((left ∩ right) \ faulty).Nonempty)

/-- The executable checker is both sound and complete for a fixed committee,
threshold, and fault set. Enumeration is exponential in committee size. -/
theorem checkSafety_iff (committee : Finset ℕ) (q : ℕ) (faulty : Finset ℕ) :
    checkSafety committee q faulty = true ↔
      ∀ left right, IsQuorum committee q left → IsQuorum committee q right →
        ∃ v, v ∈ left ∧ v ∈ right ∧ v ∉ faulty := by
  simp only [checkSafety, decide_eq_true_eq, Finset.mem_powerset]
  constructor
  · intro h left right hl hr
    obtain ⟨v, hv⟩ := h left hl.1 right hr.1 hl.2 hr.2
    rcases Finset.mem_sdiff.mp hv with ⟨hboth, hhonest⟩
    exact ⟨v, (Finset.mem_inter.mp hboth).1, (Finset.mem_inter.mp hboth).2, hhonest⟩
  · intro h left hl right hr hql hqr
    obtain ⟨v, hvl, hvr, hvh⟩ := h left right ⟨hl, hql⟩ ⟨hr, hqr⟩
    exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvl, hvr⟩, hvh⟩⟩

/-- The general proof implies that the checker accepts every safe threshold;
this is universal, not a statement only about a bounded regression sweep. -/
theorem checkSafety_of_bound {committee faulty : Finset ℕ} {q f : ℕ}
    (hf : faulty.card ≤ f) (hsafe : committee.card + f < q + q) :
    checkSafety committee q faulty = true :=
  (checkSafety_iff committee q faulty).2 fun _ _ hl hr =>
    exists_honest_intersection faulty hl hr hf hsafe

/-- A failing result really means there is a quorum pair without an honest
overlap. The certificate layer can then expose the protocol consequence. -/
theorem checkSafety_false_iff (committee : Finset ℕ) (q : ℕ) (faulty : Finset ℕ) :
    checkSafety committee q faulty = false ↔
      ∃ left right, IsQuorum committee q left ∧ IsQuorum committee q right ∧
        ¬ ∃ v, v ∈ left ∧ v ∈ right ∧ v ∉ faulty := by
  simp only [Bool.eq_false_iff, ne_eq, checkSafety_iff]
  push Not
  rfl

end LeanQuorum
