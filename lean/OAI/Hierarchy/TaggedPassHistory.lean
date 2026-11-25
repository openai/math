import OAI.Hierarchy.TaggedPassCorrect
import OAI.Hierarchy.TaggedDigitSequence

namespace OAI
/-! # Least-significant-digit refinement for the actual radix network -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage SortedBlock
open scoped Classical
noncomputable section

variable {h k j : ℕ}

theorem allowed_next (room : j+2 ≤ k) (i : ℕ) (x : state h k j i → Bool) (ok : allowed x) :
    allowed (rawRun h k j i x) :=
  (rawShape h k j i).keeps_words _ _ _ _ room (RadixRecord.Canonical h) (Or.inl rfl) x ok

/-- Refinement of the ordering of the low digits with no change of real
payload multiplicities. -/
theorem progress (room : j+2 ≤ k) (i : ℕ) (x : state h k j i → Bool) (ok : allowed x) (prev : orderedAt h k i x) :
    (RadixRecord.realWords h (rawRun h k j i x)).Perm (RadixRecord.realWords h x) ∧ orderedAt h k (i+1) (rawRun h k j i x) := by
  let d := RadixRecord.digit h k i
  let next := rawRun h k j i x
  have tick := (rawShape h k j i).correct (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h) d
    room (blank_real h) (by simp [blank_real,blank_dummy]) x (flags_allowed x ok)
  change (RadixRecord.realWords h next).Pairwise (fun a b => readKey d a ≤ readKey d b) ∧
    ∀a,bucket (readKey d) a (RadixRecord.realWords h next) = bucket (readKey d) a (RadixRecord.realWords h x) at tick
  exact refine_digit i x next (allowed_next room i x ok) prev tick

/-- The semantic invariant accumulated through the actual consecutive array
maps, including the extra flag digit. -/
theorem history (room : j+2 ≤ k) (n : ℕ) (x : Fin (pins h h) → Bool) :
    let start := Sum.elim x id ∘ RadixRecord.feed h
    let last := advance (state h k j) (rawRun h k j) n start
    allowed last ∧ (RadixRecord.realWords h last).Perm (RadixRecord.realWords h start) ∧ orderedAt h k (n+1) last := by
  apply history_of_steps
  intro i rows ok prev
  exact ⟨allowed_next room i rows ok,progress room i rows ok prev⟩

theorem final_order (room : j+2 ≤ k) (n : ℕ) (cover : h+1 ≤ (n+1)*k) (x : Fin (pins h h) → Bool) :
    let start := Sum.elim x id ∘ RadixRecord.feed h
    let last := advance (state h k j) (rawRun h k j) n start
    (RadixRecord.realWords h last).Perm (RadixRecord.realWords h start) ∧
      ((RadixRecord.realWords h last).map RadixRecord.keyValue).Pairwise (·≤·) := by
  obtain ⟨_,perm,ordered⟩ := history room n x
  exact ⟨perm,ordered_cover n cover _ ordered⟩

end
end Hierarchy.Tagged.Radix

end OAI
