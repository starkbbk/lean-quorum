import LeanQuorum.Intersection

/-!
# Agreement of quorum certificates

`votes v a` represents an authenticated vote by validator `v` for value `a` in
one fixed voting instance (for example, one height and round). Authentication
and the honest no-double-vote rule are assumptions of the model.
-/

namespace LeanQuorum

variable {Validator Value : Type*} [DecidableEq Validator]

/-- Honest validators cannot vote for two distinct values in the same instance. -/
def HonestVotes (faulty : Finset Validator) (votes : Validator → Value → Prop) : Prop :=
  ∀ v, v ∉ faulty → ∀ a b, votes v a → votes v b → a = b

/-- The signer set is explicit and deduplicated. -/
structure Certificate (committee : Finset Validator) (q : ℕ)
    (votes : Validator → Value → Prop) (value : Value) where
  signers : Finset Validator
  quorum : IsQuorum committee q signers
  supports : ∀ v ∈ signers, votes v value

/-- Agreement works for unequal certificate thresholds too. -/
theorem certificate_agreement {committee : Finset Validator} {qLeft qRight f : ℕ}
    {votes : Validator → Value → Prop} {a b : Value} (faulty : Finset Validator)
    (honest : HonestVotes faulty votes) (hf : faulty.card ≤ f)
    (hsafe : committee.card + f < qLeft + qRight)
    (left : Certificate committee qLeft votes a)
    (right : Certificate committee qRight votes b) : a = b := by
  obtain ⟨v, hvl, hvr, hvh⟩ :=
    exists_honest_intersection faulty left.quorum right.quorum hf hsafe
  exact honest v hvh a b (left.supports v hvl) (right.supports v hvr)

theorem bft_certificate_agreement {committee : Finset Validator} {f : ℕ}
    {votes : Validator → Value → Prop} {a b : Value} (faulty : Finset Validator)
    (honest : HonestVotes faulty votes) (hf : faulty.card ≤ f)
    (hn : committee.card = 3 * f + 1)
    (left : Certificate committee (2 * f + 1) votes a)
    (right : Certificate committee (2 * f + 1) votes b) : a = b :=
  certificate_agreement faulty honest hf (by omega) left right

/-- If distinct values have certificates, every common signer is faulty.
This is a precise accountability statement even below the safe threshold. -/
theorem conflicting_overlap_is_faulty {committee : Finset Validator} {qLeft qRight : ℕ}
    {votes : Validator → Value → Prop} {a b : Value} (faulty : Finset Validator)
    (honest : HonestVotes faulty votes) (hab : a ≠ b)
    (left : Certificate committee qLeft votes a)
    (right : Certificate committee qRight votes b) :
    left.signers ∩ right.signers ⊆ faulty := by
  intro v hv
  by_contra h
  exact hab (honest v h a b
    (left.supports v (Finset.mem_inter.mp hv).1)
    (right.supports v (Finset.mem_inter.mp hv).2))

/-- Conflicting certificates reveal a lower bound on the number of faults. -/
theorem conflicting_certificates_fault_bound {committee : Finset Validator}
    {qLeft qRight : ℕ} {votes : Validator → Value → Prop} {a b : Value}
    (faulty : Finset Validator) (honest : HonestVotes faulty votes) (hab : a ≠ b)
    (left : Certificate committee qLeft votes a)
    (right : Certificate committee qRight votes b) :
    qLeft + qRight ≤ committee.card + faulty.card := by
  have hi := intersection_card_bound left.quorum.1 right.quorum.1
  have hf := Finset.card_le_card
    (conflicting_overlap_is_faulty faulty honest hab left right)
  have hl := left.quorum.2
  have hr := right.quorum.2
  omega

/-- Recording more votes preserves a certificate that already exists. -/
def Certificate.extend {committee : Finset Validator} {q : ℕ}
    {votes moreVotes : Validator → Value → Prop} {a : Value}
    (cert : Certificate committee q votes a)
    (hExtension : ∀ v value, votes v value → moreVotes v value) :
    Certificate committee q moreVotes a where
  signers := cert.signers
  quorum := cert.quorum
  supports := fun v hv => hExtension v a (cert.supports v hv)

/-- Safety across two snapshots follows if the combined vote relation obeys
the honest rule. Separate per-snapshot honesty would be insufficient. -/
theorem agreement_across_snapshots {committee : Finset Validator} {q f : ℕ}
    {earlier later : Validator → Value → Prop} {a b : Value}
    (faulty : Finset Validator) (honest : HonestVotes faulty later)
    (hExtension : ∀ v value, earlier v value → later v value)
    (hf : faulty.card ≤ f) (hsafe : committee.card + f < q + q)
    (left : Certificate committee q earlier a)
    (right : Certificate committee q later b) : a = b :=
  certificate_agreement faulty honest hf hsafe (left.extend hExtension) right

end LeanQuorum
