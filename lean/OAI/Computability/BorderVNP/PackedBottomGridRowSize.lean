import OAI.Computability.BorderVNP.PackedBottomGridSite
import OAI.Computability.BorderVNP.PackedBankRoundRowSize

/-! # Public row sizes and references at the actual grid birth sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)
variable (copies capFine capReport : ℕ)

local notation "s" => born N cell position pack width owner lane aligned siteID edgeID portID channelID
  groupID v rules copies capFine capReport

/-- The bottom-grid row list has one five-field box reference at index zero,
followed only by nine-field equalities. This is the base case of the fixed
row bound carried through all crossing rounds. -/
theorem born_schema_rowBound : (s).Schema ∧ (s).RowBound 9 := by
  have rows (r : Record) (hr : r ∈ (s).rows) :
      (r.BoxRefFits (s).boxes.length ∧ r.ProfileWidthOK) ∧ (Packet.record r).length ≤ 9 := by
    simp only [born,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,
      List.singleton_append,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨⟨by change 0 < 1; decide,trivial⟩,by change 5 ≤ 9; decide⟩
    · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨⟨trivial,trivial⟩,Nat.le_refl 9⟩
  exact ⟨fun r hr => (rows r hr).1,fun r hr => (rows r hr).2⟩

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
