import OAI.Hierarchy.DescentOrdinaryRawControlsRAM
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Work of the two measured parent-control reads -/
namespace Hierarchy.DescentOrdinarySignedMeta.RawControls
open DescentPackedZip DescentPacking.PackedMatch.Local ProtocolRAM

/-- Both controls read the same eleven previous fields and the previous mark bit. -/
theorem expression_work (tab : Fin 11 → Tables) (fields : Fin 11 → Expr) (bit : Expr)
    (lut : Tables) (limit : ℕ) (cost : ∀ i, (fields i).work ≤ limit) :
    (lut.read (Gather.assembly tab fields) bit).work ≤
      1 + 11 * (limit + 11) + bit.work + 11 := by
  have subtotal := Gather.collect_work tab fields (List.finRange 11) limit cost
  rw [List.length_finRange] at subtotal
  rw [DescentPackedZip.work]
  exact Nat.add_le_add_right (Nat.add_le_add_right subtotal _) _

end Hierarchy.DescentOrdinarySignedMeta.RawControls

end OAI
