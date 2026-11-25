import OAI.Hierarchy.ProtocolRAMCalendarArena

namespace OAI
/-! # Earlier physical mode addresses for a finite mesh -/
namespace Hierarchy.ProtocolRAM.Calendar

def agrees (c : Mesh) (H J : Attempt→ℕ) : Attempt→Prop
  | .outer p a =>
    (∀ i<p,H (.outer i (c.outerFuel-1))=J (.outer i (c.outerFuel-1))) ∧
    ∀ i<a,H (.outer p i)=J (.outer p i)
  | .inner p a j b =>
    H (.outer p a)=J (.outer p a) ∧
    (∀ i<j,H (.inner p a i (c.innerFuel-1))=J (.inner p a i (c.innerFuel-1))) ∧
    ∀ i<b,H (.inner p a j i)=J (.inner p a j i)

private theorem successive (i j width : ℕ) (prior : i<j) :
    i*width+width≤j*width := by
  simpa [Nat.succ_mul] using Nat.mul_le_mul_right width (Nat.succ_le_of_lt prior)

theorem agrees_earlier (c : Mesh) (H J : Attempt→ℕ) (a : Attempt)
    (prior : ∀b,position c (.attempt b)<position c (.attempt a)→H b=J b) :
    agrees c H J a := by
  have trialPos : 0<trialSize c := by unfold trialSize;omega
  have slicePos : 0<sliceSize c := by unfold sliceSize;omega
  cases a with
  | outer p a =>
    constructor
    · intro i hi
      apply prior
      have hi':=successive i p (phaseSize c) hi
      have last:=Nat.mul_le_mul_right (trialSize c) (Nat.sub_le c.outerFuel 1)
      change i*phaseSize c+(c.outerFuel-1)*trialSize c<p*phaseSize c+a*trialSize c
      have upper : (c.outerFuel-1)*trialSize c<phaseSize c := by unfold phaseSize;omega
      omega
    · intro i hi
      apply prior
      change p*phaseSize c+i*trialSize c<p*phaseSize c+a*trialSize c
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi trialPos) _
  | inner p a j b =>
    refine ⟨prior _ ?_,?_,?_⟩
    · change trialBase c p a<trialBase c p a+1+j*sliceSize c+b
      omega
    · intro i hi
      apply prior
      change trialBase c p a+1+i*sliceSize c+(c.innerFuel-1)<trialBase c p a+1+j*sliceSize c+b
      have gap:=successive i j (sliceSize c) hi
      have prev : c.innerFuel-1<sliceSize c := by unfold sliceSize;omega
      omega
    · intro i hi
      apply prior
      exact Nat.add_lt_add_left hi _

end Hierarchy.ProtocolRAM.Calendar

end OAI
