import OAI.Hierarchy.DescentPrivateMaskPeriod
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # Cost of the emitted private mask program and its three projected fields -/
namespace Hierarchy.DescentPrivateMaskDeck.Shape
open DescentSIMDLookup DescentStaticWordColumn DescentSixParty.Chronology ProtocolRAM
noncomputable section

variable (A : DescentPrivateMaskDeck.Shape)

/-- The three nested lookups read the prior pitch, its root page and the masked field. -/
theorem field_work (base : ℕ) (pitch : DescentContactPreROM.Layout) (pages : A.RootPages)
    (i : Fin A.fields) : (A.fieldTerm base pitch pages i).work ≤ 17 := by
  unfold fieldTerm incoming
  dsimp only
  split <;> exact of_decide_eq_true rfl

def periodPrice :=
  5000*(A.count + DescentResetStemProject.volume A.fields (A.oldHosts*A.shapes)
    A.groups A.blocks A.metaBits A.oldBatch A.batch)

/-- Includes one literal write per dictionary word, the prior-pitch read for every
retained host row, and the reshaping passes for the three fields of each key. -/
theorem issued_price (base : ℕ) (pitch : DescentContactPreROM.Layout) (pages : A.RootPages)
    (w : ℕ) (old : 0 < A.oldBatch) (blocks : 0 < A.blocks) (batch : 0 < A.batch) :
    A.ticks base pitch pages + 7*names (A.code base pitch pages w) ≤ A.periodPrice := by
  let H := A.oldHosts*A.shapes
  let G := A.groups*A.blocks
  let V := DescentResetStemProject.volume A.fields H A.groups A.blocks A.metaBits A.oldBatch A.batch
  have charge := DescentResetStemProjectExpr.tariff (A.projected base) H A.groups A.blocks
    A.metaBits A.oldBatch A.batch w (A.fieldTerm base pitch pages) 17
    (A.field_work base pitch pages) old blocks batch
  change _ + 7*_ ≤ 4096*V+(4+A.fields*(4+H*chunks G A.oldBatch*(2*17+4)))+
    7*(15+A.fields*(11+4*17)) at charge
  have size : names (A.wordsPhase w base).program = 15*(A.count+1) :=
    DescentStaticWordColumn.names_mount w base A.literal A.count
  have gather : A.fields*(4+H*chunks G A.oldBatch*(2*17+4)) =
      4*A.fields+38*((A.fields*H)*chunks G A.oldBatch) := by ring
  rw [gather] at charge
  have pos : 1 ≤ V := by dsimp only [V,DescentResetStemProject.volume]; omega
  have fieldBound : A.fields ≤ V := by dsimp only [V,DescentResetStemProject.volume]; omega
  have rows : (A.fields*H)*chunks G A.oldBatch ≤ V := by
    dsimp only [V,DescentResetStemProject.volume,Overlap.rows,G]
    omega
  rw [ticks,code,names_seq,size]
  change (4+10*A.count + DescentResetStemProjectExpr.ticks _ H _ _ _ _ _ _) +
      7*(15*(A.count+1)+names (DescentResetStemProjectExpr.program _ H _ _ _ _ _ _ w)) ≤
      5000*(A.count+V)
  omega

theorem priced (base : ℕ) (pitch : DescentContactPreROM.Layout) (pages : A.RootPages)
    {w : ℕ} (old : 0 < A.oldBatch) (batch : 0 < A.batch) (blocks : 0 < A.blocks)
    (fits : ∀ i,(A.fieldTerm base pitch pages i).Fits w (A.projected base))
    (roof : A.endAddress base < 2^w) :
    let phase := A.phase base pitch pages batch blocks fits roof
    phase.ticks+7*names phase.program ≤ A.periodPrice :=
  A.issued_price base pitch pages w old blocks batch

end
end Hierarchy.DescentPrivateMaskDeck.Shape

end OAI
