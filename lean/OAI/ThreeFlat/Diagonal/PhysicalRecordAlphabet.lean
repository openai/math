import OAI.ThreeFlat.Diagonal.ShrinkTable
import OAI.ThreeFlat.Diagonal.RefreshFixedGrid

namespace OAI
/-! # Alphabet sizes of fixed physical record tables -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

def shrinkSymbolBound (T : ShrinkMotif.Table F) :=
  Finset.univ.sup (fun j : T.Row => Fintype.card (T.block j).Alphabet)

/-- A constant prior to all instances of the old physical stage. -/
def refreshSymbolBound {s h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) :=
  Finset.univ.sup (fun j : Fin (T.last+1) => Fintype.card (T.block j).Alphabet)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
