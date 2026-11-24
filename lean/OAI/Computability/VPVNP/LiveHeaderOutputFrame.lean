import OAI.Computability.VPVNP.LiveHeaderComplete
import OAI.Computability.VPVNP.LiveNominationSweep

/-!
# Memory passed from the live header into the nomination phase

The enclosing stage tag lies after the processor array and before header
scratch. Updating that tag preserves all decoded fields. The end of the
header allocation also gives the zero-initialization property used for the
auxiliary shadow, including after the nominations are stored.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors
open LiveHeader ChainAssignments PrimedInputRAM

variable {s : Sizes} {base d w : ℕ} {hw : 4 ≤ w} {advice : CutSchedule.Bits s.advice}
  {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag} {m : Memory w}

private theorem scalar_lower (b : ℕ) (f : Metadata.Field) : b ≤ f.address b := by
  cases f with
  | width i => cases i <;> simp [Metadata.Field.address,widthAddr]
  | flag i => cases i <;> simp [Metadata.Field.address,flagAddr]
  | firstTail | mode => simp [Metadata.Field.address,firstTailAddr,tagAddr]

private theorem payload_lower (s : Sizes) (base : ℕ) : base ≤ exteriorBase s base .left := by
  dsimp [exteriorBase,adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]
  omega

/-- Updating the outer dispatch cell keeps the complete physical output
image. Its value may change more than once before nominations begin. -/
theorem Output.write_outer (out : Output s base d hw advice cuts g tag m) (addr v : Word w)
    (afterSites : 2^d ≤ addr.val) (below : addr.val < base) :
    Output s base d hw advice cuts g tag (writeMemory m addr v) := by
  have hi (a : ℕ) (ha : base ≤ a) : writeMemory m addr v a = m a := ite_eq_right (by omega)
  have indexLow : base ≤ leftIndexBase s base := by
    dsimp [leftIndexBase,populationAddr,highAddr,indexBase]; omega
  have indexRight : leftIndexBase s base ≤ rightIndexBase s base := Nat.le_add_right ..
  have advLow : rightIndexBase s base ≤ adviceBase s base := Nat.le_add_right ..
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor
    · intro j
      rw [writeMemory,ite_eq_right (by have := j.isLt; omega),out.sources.headers]
    · intro side
      rw [hi, out.sources.width]
      cases side <;> simp [widthAddr]
    · rw [hi (tagAddr base) (Nat.le_add_right ..),out.sources.mode]
    · rw [hi (flagAddr base .firstHalf) (Nat.le_add_right ..),out.sources.half]
    · rw [hi (firstTailAddr base) (Nat.le_add_right ..),out.sources.firstTail]
  · intro f
    rw [hi _ (scalar_lower base f)]
    exact out.scalars f
  · intro i
    rw [hi _ (by omega),out.adviceWords i]
  · intro i h
    rw [hi _ (by omega),out.primedLeft i h]
  · intro i h
    rw [hi _ (by omega),out.primedRight i h]
  · obtain ⟨before,zero,img⟩ := out.fieldImage
    refine ⟨writeMemory before addr v,?_,?_,?_⟩
    · intro a low
      have lower := payload_lower s base
      rw [writeMemory,ite_eq_right (by omega),zero a low]
    · intro k hk hf
      apply (img.copies k hk hf).congr
      intro j _
      exact hi _ (by have := Fields.before_destination s base (Fields.key k).1 (Fields.key k).2 hf; omega)
    · intro a safe
      by_cases eq : a = addr.val
      · simp only [writeMemory,eq,ite_true]
      · simp only [writeMemory,ite_eq_right eq,img.frame a safe]

/-- Unallocated scratch beyond the header stays at the RAM's zero default. -/
theorem Output.fresh_after_limit (out : Output s base d hw advice cuts g tag m) (a : ℕ) (high : limit s base ≤ a) :
    m a = 0 := by
  obtain ⟨before,zero,img⟩ := out.fieldImage
  have h := limit_eq s base
  apply (img.frame a ?_).trans
  · apply zero
    exact ((Nat.le_add_right _ (s.capacity .exterior)).trans (dest_bounds s base .left .exterior (by decide)).2).trans high
  · refine ⟨by omega,by dsimp [offsetAddr]; omega,by dsimp [countAddr]; omega,?_⟩
    intro side f hf
    exact Or.inr ((Nat.add_le_add_left (Fields.interval_capacity s g tag side f) _).trans
      ((dest_bounds s base side f hf).2.trans high))

/-- Storing the nominated histogram preserves the header banks and leaves
every later address at the header's original zero default. -/
theorem Output.nomination_frame {T b : ℕ} (out : Output s base d hw advice cuts g tag m)
    (muBase : Word w) (muFit : muBase.val+T ≤ 2^w) (afterHeader : limit s base ≤ muBase.val)
    (μ : Fin T → Word b) :
    (∀ a < limit s base, LiveNominations.stored muBase muFit μ m a = m a) ∧
    (∀ a, muBase.val+T ≤ a → LiveNominations.stored muBase muFit μ m a = 0) := by
  constructor
  · intro a ha
    exact LiveNominations.stored_outside muBase muFit μ m a (Or.inl (ha.trans_le afterHeader))
  · intro a ha
    exact (LiveNominations.stored_outside muBase muFit μ m a (Or.inr ha)).trans (out.fresh_after_limit a (by omega))

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
