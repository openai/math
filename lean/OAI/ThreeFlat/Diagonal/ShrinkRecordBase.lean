import OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily

namespace OAI
/-! # Cardinality of the predecessor after the shrink lane cast -/
namespace ThreeFlat.Diagonal.PhysicalStage
open CompressorPacking

theorem shrink_record_base (s rem : ℕ) (A : State (2^s) (shrinkCharge s+rem)) :
    Fintype.card (shrinkRecordState s rem A).Base=Fintype.card A.Base := by
  have h {n i j : ℕ} (eqv : i=j) (a : State n i) :
      Fintype.card (eqv ▸ a : State n j).Base=Fintype.card a.Base := by cases eqv;rfl
  exact h _ A

end ThreeFlat.Diagonal.PhysicalStage

end OAI
