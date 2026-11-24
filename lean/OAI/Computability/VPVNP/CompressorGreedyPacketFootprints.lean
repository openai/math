import OAI.Computability.VPVNP.CompressorGreedyPrepareScanAccess
import OAI.Computability.VPVNP.CompressorGreedyProjectionAccess
import OAI.Computability.VPVNP.CompressorGreedyReaderAccess
import OAI.Computability.VPVNP.CompressorGreedyVisitWalk

/-!
# Physical memory bounds for the six greedy packets

The color and offset initializers read the old forward and inverse mate
columns and write their own directories. Together with tag projection,
zero publication and the two readers, each stage reads from the level
data and writes only into the fresh greedy allocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM Compression Greedy GreedyArena
open scoped Fin.CommRing

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w}
    {m : Memory w} (r : GreedyArena.Run X T origin m)

local notation "N" => Fintype.card X.Base
local notation "limit" => greedyStop origin N a

namespace GreedyArena.Run

include r in
private theorem mate_cells (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val)
    (e : X.Base × Fin (2^a)) (b : Word w) (hb : b ∈ [T.baseOut, T.baseIn]) :
    PrepareAccess.Interval lo limit (b + portNumber X.baseIndex e).val := by
  have col (c : Fin 6) : PrepareAccess.Interval lo limit (T.column c + portNumber X.baseIndex e).val := by
    have idx : (portNumber (w := w) X.baseIndex e).val < N * 2^a := by
      change (IncidenceDirectory.basePort (w := w) X e).val < _
      rw [IncidenceDirectory.basePort_number]
      exact (Nat.mod_le _ _).trans_lt (IncidenceDirectory.baseOrder X e).isLt
    have bound := r.old c
    have mul := Nat.mul_le_mul_right (2^a) (Nat.le_mul_of_pos_right N (Nat.two_pow_pos (packingLaneBits a g)))
    have room := r.room
    have h := bounds origin N a
    change origin+N ≤ _ ∧ _ at h
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    exact ⟨(low c).trans (Nat.le_add_right ..), by omega⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact col 0
  · obtain rfl := List.mem_singleton.mp hb
    exact col 1

/-- The relocated color initializer reads old mates and writes only its fresh
color labels, headers and operand pointers. -/
theorem color_prepare_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) :
    LogAccess (PrepareAccess.Interval lo limit) (PrepareAccess.Interval origin limit) r.color.prep := by
  let L := colorLayout w origin N a r.room
  let U := colorTables T origin N a
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have room := r.room
  have src := PrepareAccess.scan L U X.slots.base X.baseIndex (colorOperandRows (2^a))
    (projectedMemory X T origin m) rfl r.color_tables
    (by change offsetBase origin N a < 2^w; omega) (r.old.graphOutside L le_rfl _ _ _)
    (fun _ ↦ rowWords_color_length _ _ _ _) (PrepareAccess.Interval lo limit) (mate_cells r lo low) _ r.color.prepRun
  exact src.mono (fun _ hz ↦ hz) (fun x ⟨h₁,h₂⟩ ↦ by
    change origin ≤ x at h₁
    change x < offsetBase origin N a at h₂
    exact ⟨h₁, by omega⟩)

/-- The offset initializer follows the same old mate columns and writes its
disjoint offset directory. -/
theorem tag_prepare_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) :
    LogAccess (PrepareAccess.Interval lo limit) (PrepareAccess.Interval origin limit) r.offsets.prep := by
  let L := tagLayout w origin N a r.room
  let U := tagTables T origin N a
  have h := bounds origin N a
  change origin+N ≤ _ ∧ _ at h
  have room := r.room
  have src := PrepareAccess.scan L U X.slots.base X.baseIndex (tagOperandRows (2^a))
    r.color.post rfl r.offset_tables
    (by change shiftBase origin N a < 2^w; omega)
    (r.old.graphOutside L (by change origin ≤ offsetBase origin N a; omega) _ _ _)
    (fun _ ↦ by rw [rowWords_tag_length, tagTests_length, Nat.mul_comm]) (PrepareAccess.Interval lo limit)
    (mate_cells r lo low) _ r.offsets.prepRun
  exact src.mono (fun _ hz ↦ hz) (fun x ⟨h₁,h₂⟩ ↦ by
    change offsetBase origin N a ≤ x at h₁
    change x < shiftBase origin N a at h₂
    exact ⟨by omega, by omega⟩)

end GreedyArena.Run

namespace GreedyVisit

/-- Per-packet memory bounds in native execution order. The lower read bound
may be any common lower bound for the six old incidence columns. -/
theorem packet_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (j : Stage) :
    LogAccess (PrepareAccess.Interval lo limit) (PrepareAccess.Interval origin limit) (packetReports r j) := by
  cases j with
  | extract => exact r.projection_access lo low
  | zero => exact r.zero_access lo
  | colorPrepare => exact r.color_prepare_access lo low
  | colorRead => exact r.color_read_access lo low
  | tagPrepare => exact r.tag_prepare_access lo low
  | tagRead => exact r.tag_read_access lo low

end GreedyVisit

end CompressorRecords

end VPVNP
end Computability
end OAI
