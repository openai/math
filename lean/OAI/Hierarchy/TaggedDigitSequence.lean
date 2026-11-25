import OAI.Hierarchy.TaggedPassState
import OAI.Hierarchy.TaggedDigitHistory
import OAI.Hierarchy.TaggedRadixStages

namespace OAI
/-! # Consecutive physical arrays in the low-digit-first radix schedule -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage SortedBlock
open scoped Classical
noncomputable section

variable {h k j : ℕ}

def rawShape (h k j i : ℕ) : PassShape := ⟨k,j,slotSequence (2^(h+1)) k j i⟩
abbrev state (h k j i : ℕ) := RowBits (slotSequence (2^(h+1)) k j i) (RadixRecord.width h)

def rawRun (h k j i : ℕ) : (state h k j i → Bool) → (state h k j (i+1) → Bool) :=
  (rawShape h k j i).run (RadixRecord.blank h) (RadixRecord.real h) (RadixRecord.dummy h) (RadixRecord.digit h k i)

theorem flags_allowed {n : ℕ} (x : RowBits n (RadixRecord.width h) → Bool) (ok : allowed x) :
    PassShape.shapeFlags n (RadixRecord.real h) (RadixRecord.dummy h) x := by
  intro i
  rcases ok i with z|⟨re,du,_⟩
  · have a := congrFun z (RadixRecord.real h); have b := congrFun z (RadixRecord.dummy h)
    simp only [blank_real,blank_dummy] at a b; simp [a,b]
  · simp [du,re]

theorem history_of_steps
    (step : ∀ i (x : state h k j i → Bool), allowed x → orderedAt h k i x →
      let next := rawRun h k j i x
      allowed next ∧ (RadixRecord.realWords h next).Perm (RadixRecord.realWords h x) ∧ orderedAt h k (i+1) next) (n : ℕ) (x : Fin (pins h h) → Bool) :
    let start := Sum.elim x id ∘ RadixRecord.feed h
    let last := advance (state h k j) (rawRun h k j) n start
    allowed last ∧ (RadixRecord.realWords h last).Perm (RadixRecord.realWords h start) ∧ orderedAt h k (n+1) last := by
  let feed := Sum.elim x id ∘ RadixRecord.feed h
  have start : allowed feed := RadixRecord.canonical_feed x
  induction n with
  | zero =>
    apply step 0 feed start
    unfold orderedAt
    apply List.pairwise_of_forall_mem_list
    intro u _ v _
    simp only [pow_zero,Nat.mod_one,le_refl]
  | succ n ih =>
    obtain ⟨before,perm,old⟩ := ih
    obtain ⟨after,next,tick⟩ := step (n+1) _ before old
    exact ⟨after,next.trans perm,tick⟩

end
end Hierarchy.Tagged.Radix

end OAI
