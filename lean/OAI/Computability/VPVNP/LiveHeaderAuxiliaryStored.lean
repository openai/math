import OAI.Computability.VPVNP.LiveHeaderAuxiliaryArrays
import OAI.Computability.VPVNP.LiveHeaderOutputFrame

/-!
# Auxiliary source arrays after the nomination handoff

The nomination sweep writes its histogram above the live header allocation.
The outer stage tag lies below all seven source arrays, so their contents
are available at the start of the auxiliary stage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM LiveHeaderSchedule LiveHeader ChainAssignments CutSchedule
open scoped Fin.CommRing

variable {s : Sizes} {base d w t Z T b stages : ℕ} {hw : 4 ≤ w} {advice : Bits s.advice}
variable {cuts : AllCuts s.h s.delta} {tag : Mode.Tag} {m : Memory w}

/-- The memory passed by the nomination stage contains the six decoded header
arrays and the nominated counters in their public source ranges. -/
theorem Output.auxiliaryStoredInputArrays (i : Fin (2^s.h))
    (out : Output s base d hw advice cuts (halves s.h (.inl i)) tag m)
    (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta)
    (muBase : Word w) (muFit : muBase.val+T ≤ 2^w) (afterHeader : limit s base ≤ muBase.val)
    (μ : Fin T → Word b) (outer : Word w) (dest : Option (Fin stages)) (below : outer.val ≤ base) :
    let L := PairedChain.lengths s.h s.delta s.advice i
    let ξ := exteriorOf fit (liveCutEquiv s.h s.delta cuts).1
    let hist := List.ofFn fun k => Fin.ofNat (2^w) (μ k).val
    LiveAuxiliaryHeaders.InputArrays L (PairedChain.headers advice ξ i) hist
      (LiveAuxiliaryStages.headerSources s base muBase)
      (LiveStageLink.transferMemory outer dest (LiveNominations.stored muBase muFit μ m)) := by
  dsimp only
  have unchanged (a : ℕ) (ha : base < a) :
      LiveStageLink.transferMemory outer dest (LiveNominations.stored muBase muFit μ m) a =
        LiveNominations.stored muBase muFit μ m a := by
    cases dest <;> simp [LiveStageLink.transferMemory, writeMemory, (below.trans_lt ha).ne']
  apply out.auxiliaryInputArrays i ev he fit (afterHeader.trans muBase.isLt.le)
  · intro a lo hi
    exact (unchanged a lo).trans ((out.nomination_frame muBase muFit afterHeader μ).1 a hi)
  · intro j
    have hj : j.val < T := by simpa only [List.length_ofFn] using j.isLt
    have addr : (muBase + (j.val : Word w)).val = muBase.val+j.val := by
      have hj' : ((j.val : Word w) : ℕ) = j.val := Fin.val_cast_of_lt (by omega)
      rw [Fin.val_add_eq_of_add_lt (by rw [hj']; omega), hj']
    have lo : base < muBase.val := by rw [limit_eq] at afterHeader; omega
    rw [addr, unchanged _ (by omega)]
    change _ = (List.ofFn fun k => Fin.ofNat (2^w) (μ k).val)[j.val]
    rw [List.getElem_ofFn]
    exact LiveNominations.stored_at muBase muFit μ m ⟨j.val,hj⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
