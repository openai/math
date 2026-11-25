import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention

/-! # Actual occupied-width pointer and full square array after the owned return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA RoutingISA.Evaluator RoutingISA.CubeArena RoutingISA.LocalRow
open private array_word from OAI.Computability.BorderVNP.CubeRouteCommonOwners

/-- The original interval directory supplies both the width-array pointer and
all its occupied bin widths in the later returned host memory. -/
theorem owned_widths {ar : CubeArena.Layout} {il : NativeIntervals.Layout} {frame controls R broadcast : ℕ}
    {axis : Fin (ar.n+1)} {before dir initial written mem : ℕ → ℕ}
    (keep : FiniteEvaluator.CubeAllocation.HostRetention ar frame initial written mem)
    (entry : NativeEntry ar frame controls axis R (powerHeaderImage ar broadcast dir) initial written)
    (atFrame : il.frame=frame) (fields : il.Fields before) (image : il.Image before il.count dir)
    (low : ∀ x < ar.publicBase, dir x=initial x) (width : il.widths=ar.widthBase) (ord : il.ordinals=ar.ordinalBase) :
    mem (frame+57)=ar.widthBase ∧ ∀ k < ar.alphabet^2, mem (ar.widthBase+k)=dir (il.widths+k) := by
  have primary := keep.primary
  have header := ar.writer_order.1
  obtain ⟨_,_,_,_,widthLo,ordinalLo,_,powHi,groupHi,teamHi,pairHi,hostHi,recordHi⟩ := ar.group_order
  have widthEnd : ar.widthBase+ar.alphabet^2=ar.ordinalBase := rfl
  have ordEnd : ar.ordinalBase+ar.cables=ar.powerBase := rfl
  obtain ⟨scheduled,res,im⟩ := entry.image
  constructor
  · have ptr := fields.2.2.2.2.1
    rw [atFrame,width] at ptr
    have preserved := image.outside (frame+57) (by rw [width]; omega) (by rw [ord]; omega)
    exact (keep.lower _ (by omega) (by omega) (by omega)).trans ((low _ (by omega)).symm.trans (preserved.trans ptr))
  · intro k hk
    have lo : ar.publicBase ≤ ar.widthBase+k := by omega
    have hi : ar.widthBase+k < ar.powerBase := by omega
    rw [width]
    exact (keep.tables _ lo (by omega)).trans ((scheduled_before ar res im.pairRows
      ⟨rfl,rfl,rfl,rfl,rfl⟩ (by omega)).trans (array_word ar dir broadcast lo hi))

end Cube.Padding

end BorderVNP
end Computability
end OAI
