import OAI.Hierarchy.ProtocolRAMStripEdgeSupport

namespace OAI
/-! # Public core and original bought role operands after a native occurrence guard -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing

variable {w : ℕ} {S : PurchaseSampler} {h d k : ℕ} {C H A B : Type*}

theorem Board.checked_core_value (b : Board) (x : Expr) (m : Memory w) (r : Word w)
    (room : b.rows<2^w) (core : (x.eval m r).val<b.coreRows ∨ (x.eval m r).val=b.rows) :
    (b.checkedEdge x).eval m r=x.eval m r := by
  apply Fin.ext
  rw [b.checkedEdge_val _ m r room]
  rcases core with lt|eq
  · simp [lt]
  · have le : b.coreRows≤b.rows := Nat.le_add_right _ _
    simp [eq,not_lt_of_ge le]

/-- The chronological guard needs its previous purchase bit only for an
in-range noncore row. An unallocated row with raw value equal to the sentinel
has the same value on every branch. -/
theorem Board.guarded_value (b : Board) {x keep : Expr} (m : Memory w) (r : Word w)
    (room : b.rows<2^w) (bound : (x.eval m r).val≤b.rows)
    (live : b.coreRows≤(x.eval m r).val → (x.eval m r).val<b.rows → keep.eval m r≠0) :
    (StripChart.physicalEdge b keep x).eval m r=x.eval m r := by
  apply Fin.ext
  rw [physicalEdge_val b keep x m r room]
  split_ifs with core endRow off
  · rfl
  · exact False.elim (live (Nat.le_of_not_lt core) endRow off)
  · rfl
  · omega


end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
