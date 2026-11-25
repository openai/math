import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # The physical ordering of an already dense finite ordinal -/
namespace Hierarchy.DescentStageEdgeReceipt
open scoped Classical
noncomputable section
def dense {E : Type} [Fintype E] (f : E↪Fin (Fintype.card E)) : E≃Fin (Fintype.card E) :=
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).2 ⟨f.injective,by simp⟩)

end
end Hierarchy.DescentStageEdgeReceipt

namespace Hierarchy.DescentSixParty.GroupStage
open scoped Classical
noncomputable section
theorem compact_dense {E : Type} [Fintype E] (f : E↪Fin (Fintype.card E)) (x : E) :
    DescentPhysicalOrder.physical (f.trans Fin.valEmbedding) x=f x := by
  apply Fin.ext
  rw [DescentPhysicalOrder.physical_val,←Fin.card_Iio (f x)]
  apply Finset.card_bij (fun u _=>f u)
  · intro u hu
    exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hu).2
  · exact fun _ _ _ _ h=>f.injective h
  · intro j hj
    refine ⟨(DescentStageEdgeReceipt.dense f).symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · change (DescentStageEdgeReceipt.dense f) ((DescentStageEdgeReceipt.dense f).symm j)<f x
      simpa using Finset.mem_Iio.mp hj
    · exact (DescentStageEdgeReceipt.dense f).apply_symm_apply j

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
