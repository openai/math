import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Base cardinality under a lane cast and a binary refresh -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
  (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)

theorem refreshBinary_next_base (j : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    Fintype.card ((refreshBinary T A hm hh sym rows zero conn).next j).Base = Fintype.card A.Base*2^s := by
  change Fintype.card (A.Base × Fin (2^s)) = _
  rw [Fintype.card_prod,Fintype.card_fin]

namespace Program

theorem baseCast {d l l' : ℕ} (e : l=l') (A : State d l) :
    Fintype.card (e ▸ A : State d l').Base = Fintype.card A.Base := by cases e; rfl

end Program
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
