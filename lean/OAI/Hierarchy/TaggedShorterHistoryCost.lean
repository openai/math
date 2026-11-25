import OAI.Hierarchy.TaggedShorterHistorySort
import OAI.Hierarchy.TaggedShorterPullCost

namespace OAI
/-! # Cell count of the complete sorted history audit -/

noncomputable section
namespace Hierarchy
open ThreeFlat Routing Diagonal
open Tagged
open scoped Classical BigOperators

namespace TaggedShorterHistoryOrder
variable {F : Type*} [CommRing F] {m w a : ℕ}

/-- The stable-sort comparison rows and the physical predecessor array. -/
def rowPrice (m w a : ℕ) :=
  2*(7*w)+m+(m+7*w+1)+(m+7*w+2)*176+87*a*m + 4*(50*w+11)+13

theorem audit_cells (hw : 2≤w) : (audit (F:=F) (m:=m) (a:=a) hw).cells ≤ 2^m*rowPrice m w a := by
  have cut := ControlSort.size (F:=F) (m:=m) (a:=a) (id : Fin (RecordWidth w) → _)
  have scanBound := scan_cells (F:=F) (m:=m) (w:=w)
  rw [audit,TypedWiring.glue_cells,Fintype.sum_bool]
  change (predecessor (F:=F) (m:=m) hw).cells +
    (ControlSort.cut F a (id : Fin (RecordWidth w) → _)).cells ≤ _
  rw [predecessor,RadixStage.pullPins_cells]
  have core : (ControlSort.cut (m:=m) F a (id : Fin (RecordWidth w) → _)).cells ≤
      2^m*(2*(7*w)+m+(m+7*w+1)+(m+7*w+2)*176+87*a*m) := by
    simp only [recordWidth_eq] at cut ⊢
    omega
  calc
    _ ≤ _ := Nat.add_le_add scanBound core
    _ ≤ _ := by unfold rowPrice; nlinarith only [(Nat.one_le_two_pow : 1≤2^m)]

end TaggedShorterHistoryOrder

end Hierarchy

end
end OAI
