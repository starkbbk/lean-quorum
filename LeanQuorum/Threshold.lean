import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# The safety/availability threshold frontier

Safety means `n + f < 2q`. Availability here means only that all honest
validators together can form a quorum: `q + f ≤ n`. It is a cardinality
condition, not a termination or network-liveness theorem.
-/

namespace LeanQuorum

/-- The smallest symmetric threshold with an honest-overlap guarantee. -/
def minimumSafeThreshold (n f : ℕ) : ℕ := (n + f) / 2 + 1

def SafeThreshold (n f q : ℕ) : Prop := n + f < q + q

def AvailableThreshold (n f q : ℕ) : Prop := q + f ≤ n

/-- Exact characterization, including odd/even and zero-size edge cases. -/
theorem safe_iff_minimum_le (n f q : ℕ) :
    SafeThreshold n f q ↔ minimumSafeThreshold n f ≤ q := by
  unfold SafeThreshold minimumSafeThreshold
  omega

theorem minimum_is_safe (n f : ℕ) : SafeThreshold n f (minimumSafeThreshold n f) :=
  (safe_iff_minimum_le n f _).2 (Nat.le_refl _)

theorem below_minimum_is_unsafe {n f q : ℕ} (h : q < minimumSafeThreshold n f) :
    ¬ SafeThreshold n f q := by
  rw [safe_iff_minimum_le]
  omega

theorem safe_threshold_mono {n f q r : ℕ} (h : SafeThreshold n f q) (hqr : q ≤ r) :
    SafeThreshold n f r := by
  unfold SafeThreshold at *
  omega

/-- A safe and available threshold exists exactly below the one-third fault
boundary. This is an equivalence of the two stated arithmetic requirements. -/
theorem safe_available_iff (n f : ℕ) :
    (∃ q, SafeThreshold n f q ∧ AvailableThreshold n f q) ↔ 3 * f < n := by
  constructor
  · rintro ⟨q, hs, ha⟩
    unfold SafeThreshold at hs
    unfold AvailableThreshold at ha
    omega
  · intro h
    refine ⟨n - f, ?_, ?_⟩
    · unfold SafeThreshold
      omega
    · unfold AvailableThreshold
      omega

theorem minimum_is_available {n f : ℕ} (h : 3 * f < n) :
    AvailableThreshold n f (minimumSafeThreshold n f) := by
  obtain ⟨q, hs, ha⟩ := (safe_available_iff n f).2 h
  have hmin := (safe_iff_minimum_le n f q).1 hs
  unfold AvailableThreshold at *
  omega

theorem no_safe_available_threshold {n f : ℕ} (h : n ≤ 3 * f) :
    ¬ ∃ q, SafeThreshold n f q ∧ AvailableThreshold n f q := by
  rw [safe_available_iff]
  omega

theorem standard_bft_threshold (f : ℕ) :
    minimumSafeThreshold (3 * f + 1) f = 2 * f + 1 := by
  unfold minimumSafeThreshold
  omega

/-- Availability tolerates any set of at most `f` silent validators, at the
level of counts. The caller still needs a protocol to collect their votes. -/
theorem available_after_faults {n f q actualFaults : ℕ}
    (ha : AvailableThreshold n f q) (hf : actualFaults ≤ f) :
    q ≤ n - actualFaults := by
  unfold AvailableThreshold at ha
  omega

end LeanQuorum
