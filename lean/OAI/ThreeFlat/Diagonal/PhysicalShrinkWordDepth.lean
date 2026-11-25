import OAI.ThreeFlat.Diagonal.HistorySiteDepth
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly

namespace OAI
/-! # Depth of each elected root of the numbered shrink move -/

namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F]

private def rootWithin {d l D m : ℕ} {A : State d l} {R : Move F A D m} (J : R.Assembler Pins) :=
  ∀ (L : A.Words Pins) (b : Fin R.rules.count) (z : (R.rules.target b).Site),
    Tree.Within 4 ((J L b).stage.root z)

private theorem root_degree {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (h : rootWithin J) : rootWithin (Move.castAssembler e R J) := by
  cases e
  exact h

private theorem root_lanes {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (h : rootWithin J) :
    rootWithin (Move.inputAssembler e A R J) := by
  cases e
  exact h

attribute [local irreducible] CompressorPacking.shrinkSite

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem shrinkBinary_root_within (T : ShrinkMotif.Table F) (s D rem : ℕ) (hd : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    rootWithin (shrinkBinary_assembler (Pins:=Pins) T s D rem hd small A) := by
  unfold shrinkBinary_assembler
  apply root_lanes
  unfold shrinkRaw_assembler shrinkMove_assembler
  apply root_degree
  intro L h v
  apply CompressorPacking.shrinkSite_within


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
