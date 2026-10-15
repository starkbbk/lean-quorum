import LeanQuorum.Certificates

/-!
# An executable vote collector with an inductive safety invariant

The collector stores distinct `(validator, value)` pairs. Honest validators are
prevented from adding a conflicting vote. Faulty validators may equivocate.
The implementation, invariant, trace processing, and certificate agreement use
the same vote representation.
-/

namespace LeanQuorum.BallotBox

variable {Validator Value : Type*} [DecidableEq Validator] [DecidableEq Value]

abbrev Ballots (Validator Value : Type*) := Finset (Validator × Value)

def NoConflict (ballots : Ballots Validator Value) (validator : Validator)
    (value : Value) : Prop :=
  ∀ entry ∈ ballots, entry.1 = validator → entry.2 = value

instance (ballots : Ballots Validator Value) (validator : Validator) (value : Value) :
    Decidable (NoConflict ballots validator value) :=
  inferInstanceAs (Decidable (∀ entry ∈ ballots, entry.1 = validator → entry.2 = value))

/-- Faulty identities may equivocate; honest identities may only repeat their
existing value. Repeated identical pairs are deduplicated by `Finset`. -/
def submit (faulty : Finset Validator) (ballots : Ballots Validator Value)
    (validator : Validator) (value : Value) : Ballots Validator Value :=
  if validator ∈ faulty ∨ NoConflict ballots validator value then
    insert (validator, value) ballots
  else ballots

def VoteRelation (ballots : Ballots Validator Value) (validator : Validator)
    (value : Value) : Prop := (validator, value) ∈ ballots

def Invariant (faulty : Finset Validator) (ballots : Ballots Validator Value) : Prop :=
  HonestVotes faulty (VoteRelation ballots)

omit [DecidableEq Validator] [DecidableEq Value] in
theorem empty_invariant (faulty : Finset Validator) :
    Invariant (Value := Value) faulty ∅ := by
  intro v hv a b ha
  simp [VoteRelation] at ha

theorem submit_monotone (faulty : Finset Validator) (ballots : Ballots Validator Value)
    (validator : Validator) (value : Value) :
    ballots ⊆ submit faulty ballots validator value := by
  unfold submit
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem submit_accepts_faulty {faulty : Finset Validator}
    (ballots : Ballots Validator Value) {validator : Validator}
    (h : validator ∈ faulty) (value : Value) :
    (validator, value) ∈ submit faulty ballots validator value := by
  simp [submit, h]

/-- Rejection is justified by an actual conflicting stored vote. -/
theorem submit_rejects_conflict {faulty : Finset Validator}
    {ballots : Ballots Validator Value} {validator : Validator} {old value : Value}
    (hh : validator ∉ faulty) (hold : (validator, old) ∈ ballots) (hne : old ≠ value) :
    submit faulty ballots validator value = ballots := by
  have hconflict : ¬ NoConflict ballots validator value := by
    intro h
    exact hne (h (validator, old) hold rfl)
  simp [submit, hh, hconflict]

/-- One guarded state transition preserves honest no-double-voting. -/
theorem submit_preserves_invariant {faulty : Finset Validator}
    {ballots : Ballots Validator Value} (hi : Invariant faulty ballots)
    (validator : Validator) (value : Value) :
    Invariant faulty (submit faulty ballots validator value) := by
  unfold submit
  split
  next hallowed =>
    intro v hv a b ha hb
    change (v, a) ∈ insert (validator, value) ballots at ha
    change (v, b) ∈ insert (validator, value) ballots at hb
    rcases Finset.mem_insert.mp ha with hnewA | holdA
    · have hpair := Prod.mk.inj hnewA
      rcases hpair with ⟨rfl, rfl⟩
      rcases Finset.mem_insert.mp hb with hnewB | holdB
      · exact (Prod.mk.inj hnewB).2.symm
      · have hc : NoConflict ballots v a := hallowed.resolve_left hv
        exact (hc (v, b) holdB rfl).symm
    · rcases Finset.mem_insert.mp hb with hnewB | holdB
      · rcases Prod.mk.inj hnewB with ⟨rfl, rfl⟩
        have hc : NoConflict ballots v b := hallowed.resolve_left hv
        exact hc (v, a) holdA rfl
      · exact hi v hv a b holdA holdB
  next => exact hi

/-- Process an arbitrary finite trace of candidate votes. -/
def process (faulty : Finset Validator) (ballots : Ballots Validator Value) :
    List (Validator × Value) → Ballots Validator Value
  | [] => ballots
  | (validator, value) :: rest =>
    process faulty (submit faulty ballots validator value) rest

theorem process_preserves_invariant (faulty : Finset Validator)
    (trace : List (Validator × Value)) {ballots : Ballots Validator Value}
    (hi : Invariant faulty ballots) : Invariant faulty (process faulty ballots trace) := by
  induction trace generalizing ballots with
  | nil => exact hi
  | cons entry rest ih =>
    exact ih (submit_preserves_invariant hi entry.1 entry.2)

theorem process_monotone (faulty : Finset Validator)
    (trace : List (Validator × Value)) (ballots : Ballots Validator Value) :
    ballots ⊆ process faulty ballots trace := by
  induction trace generalizing ballots with
  | nil => exact Finset.Subset.refl _
  | cons entry rest ih =>
    exact (submit_monotone faulty ballots entry.1 entry.2).trans
      (ih (submit faulty ballots entry.1 entry.2))

theorem process_append (faulty : Finset Validator) (first second : List (Validator × Value))
    (ballots : Ballots Validator Value) :
    process faulty ballots (first ++ second) =
      process faulty (process faulty ballots first) second := by
  induction first generalizing ballots with
  | nil => rfl
  | cons entry rest ih => exact ih (submit faulty ballots entry.1 entry.2)

/-- End-to-end agreement for certificates built from the executable collector.
Honest no-double-voting is proved by induction over the supplied trace. -/
theorem processed_certificate_agreement {committee faulty : Finset Validator}
    {q f : ℕ} {a b : Value} (trace : List (Validator × Value))
    (hf : faulty.card ≤ f) (hsafe : committee.card + f < q + q)
    (left : Certificate committee q (VoteRelation (process faulty ∅ trace)) a)
    (right : Certificate committee q (VoteRelation (process faulty ∅ trace)) b) : a = b :=
  certificate_agreement faulty
    (process_preserves_invariant faulty trace (empty_invariant faulty)) hf hsafe left right

/-- Certificates collected before and after more input agree. Existing votes
persist, and the final combined state satisfies the proved invariant. -/
theorem processed_snapshot_agreement {committee faulty : Finset Validator}
    {q f : ℕ} {a b : Value} (first second : List (Validator × Value))
    (hf : faulty.card ≤ f) (hsafe : committee.card + f < q + q)
    (left : Certificate committee q (VoteRelation (process faulty ∅ first)) a)
    (right : Certificate committee q (VoteRelation (process faulty ∅ (first ++ second))) b) :
    a = b := by
  apply agreement_across_snapshots faulty
    (process_preserves_invariant faulty (first ++ second) (empty_invariant faulty))
    ?_ hf hsafe left right
  intro validator value hv
  change (validator, value) ∈ process faulty ∅ (first ++ second)
  rw [process_append]
  exact process_monotone faulty second (process faulty ∅ first) hv

end LeanQuorum.BallotBox
