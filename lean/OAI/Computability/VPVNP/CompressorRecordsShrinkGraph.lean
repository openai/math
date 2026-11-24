import OAI.Computability.VPVNP.CompressorRecordsShrinkScan
import OAI.Computability.VPVNP.CompressorRecordsShrinkWords

/-!
# Placement columns on the typed shrinking graph

The four output columns of the native old-position scan encode the owner, the
thickness bit, the assigned outgoing bundle and the bundle's target. The
indexed old positions include the tag, mask, slot label and residual lane.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRAM

open BurstRAM Compression PrimedStackRAM

variable {V : Type} {w a g n : ℕ}
variable (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (order : V ≃ Fin n)

/-- The number of old positions scanned for placement, counting every packing lane of each base
vertex. -/
abbrev PositionCount (n a g : ℕ) := n*2^(packingLaneBits a g)

/-- The fixed four columns as consumed by subsequent arc and preimage passes. -/
structure PlacementColumns (p : Fin 14 → Word w) (layout : Bool) (m : Memory w) : Prop where
  atSite : ∀ x : Shrink.Old V a g,
    let P := orderedDyadicPacking G order
    let i := word w (Shrink.oldNumber order x)
    ((m (outAddr p 0 i)).val, (m (outAddr p 1 i)).val,
      (m (outAddr p 2 i)).val, (m (outAddr p 3 i)).val) =
      (Shrink.packedNumber order (P.placement layout x), (decide (P.thick x)).toNat,
       Shrink.join a (Shrink.packedNumber order (P.assignedBundle x).1) (P.assignedBundle x).2.val,
       Shrink.packedNumber order (P.siteGraph.target (P.assignedBundle x)).1)

theorem ScanResult.placementColumns (p : Fin 14 → Word w) (layout : Bool) (m : Memory w)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g layout)
    (d : Shrink.Directory G order (column p m 6) (column p m 7) (column p m 8) (column p m 9))
    (hOld : PositionCount n a g ≤ 2^w)
    (hSlots : n*(2^(Shrink.J a)*2^g)*2^a ≤ 2^w) {rs : List (Report w)}
    (h : ScanResult p (PositionCount n a g) 0 (PositionCount n a g) m rs) :
    PlacementColumns G order p layout (after m (eventLog rs)) := by
  constructor
  intro x P i
  have hx : Shrink.oldNumber order x < PositionCount n a g := by
    rw [← Shrink.oldIndex_val]; exact Fin.isLt _
  have hi : i.val < 0 + PositionCount n a g := by
    change (Shrink.oldNumber order x) % (2^w) < _
    rw [Nat.mod_eq_of_lt (hx.trans_le hOld), Nat.zero_add]
    exact hx
  rw [h.readback 0 i (Nat.zero_le _) hi, h.readback 1 i (Nat.zero_le _) hi,
    h.readback 2 i (Nat.zero_le _) hi, h.readback 3 i (Nat.zero_le _) hi]
  exact outputs_exact G order p m layout hp d hOld hSlots x

/-- The shrinking scan on the entire old graph fills the typed placement arrays. -/
theorem placement_run (p : Fin 14 → Word w) (layout : Bool) (m : Memory w)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g layout)
    (d : Shrink.Directory G order (column p m 6) (column p m 7) (column p m 8) (column p m 9))
    (regions : Regions p (PositionCount n a g))
    (hSlots : n*(2^(Shrink.J a)*2^g)*2^a ≤ 2^w) :
    let N := PositionCount n a g
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 65 (some (word w 0)) m (List.replicate N []) = some rs ∧
      ScanResult p N 0 N m rs ∧ PlacementColumns G order p layout (after m (eventLog rs)) := by
  intro N M
  obtain ⟨rs,he,h⟩ := scan_run p N 0 N m regions (by omega)
  exact ⟨rs,he,h,h.placementColumns G order p layout m hp d regions.fits hSlots⟩

end CompressorRecords.ShrinkRAM

end VPVNP
end Computability
end OAI
