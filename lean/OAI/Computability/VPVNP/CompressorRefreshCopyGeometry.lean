import OAI.Computability.VPVNP.CompressorShrinkSlotFootprint

/-!
# Packed copy geometry for a selected degree refresh

The scratch columns and canonical successor columns use the full number of
output slots as their common stride. Only the populated prefix of each
column participates in the copy. The first three prefixes end after the
base ports, and the last three include all residual lanes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.CopyGeometry

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open DescriptorSpace CopyIncidence

/-- The output allocation and the canonical successor have the same
column stride, and the scratch output fits before the successor arrays. -/
structure Packed {b l : ℕ} (Y : State b l) (P : Allocation.Plan) (L : Layout)
    (level : Fin L.levels) (w : ℕ) : Prop where
  slots : Y.positions * 2^b = P.capacity
  capacity : Y.positions * 2^b ≤ slotCapacity L
  apart : P.stop ≤ incidenceStart L level
  fit : endAddress L < 2^w
  lower : levelStart L 0 ≤ P.next

namespace Packed

variable {b l w : ℕ} {Y : State b l} {P : Allocation.Plan} {L : Layout} {level : Fin L.levels}
variable (G : Packed Y P L level w)
local notation "N" => Y.positions * 2^b
local notation "T" => P.output w
local notation "U" => packedIncidence L w level N

private theorem column_end (c : Fin 6) (stride : ℕ) : c.val*stride + stride ≤ 6*stride := by
  simpa only [Nat.succ_mul] using Nat.mul_le_mul_right stride c.isLt

include G

private theorem destRoom : incidenceStart L level + 6*N < 2^w :=
  packed_incidence_room L G.fit level G.capacity

private theorem scratchRoom : P.stop < 2^w :=
  G.apart.trans_lt ((Nat.le_add_right _ _).trans_lt G.destRoom)

theorem sourceHead (c : Fin 6) : ((T).column c).val = P.next+c.val*P.capacity := by
  rw [P.output_column]
  have bound := column_end c P.capacity
  have room : P.next+6*P.capacity < 2^w := G.scratchRoom
  exact Nat.mod_eq_of_lt (by omega)

theorem destinationHead (c : Fin 6) : ((U).column c).val = incidenceStart L level+c.val*N := by
  rw [packed_column]
  have bound := column_end c N
  have room := G.destRoom
  exact Nat.mod_eq_of_lt (by unfold incidenceBase; omega)

private theorem source_end (c : Fin 6) : ((T).column c).val + rows Y c ≤ P.stop := by
  rw [G.sourceHead]
  have count := (rows_le_slots Y c).trans_eq G.slots
  have bound := column_end c P.capacity
  unfold Allocation.Plan.stop
  omega

private theorem destination_end (c : Fin 6) :
    ((U).column c).val + rows Y c ≤ incidenceStart L level + 6*N := by
  rw [G.destinationHead]
  have count := rows_le_slots Y c
  have bound := column_end c N
  omega

theorem roomT (c : Fin 6) : ((T).column c).val + rows Y c ≤ 2^w :=
  (G.source_end c).trans G.scratchRoom.le

theorem roomU (c : Fin 6) : ((U).column c).val + rows Y c ≤ 2^w :=
  (G.destination_end c).trans G.destRoom.le

theorem rowsFit (c : Fin 6) : rows Y c < 2^w :=
  (Nat.le_add_left ..).trans_lt ((G.destination_end c).trans_lt G.destRoom)

theorem regions : Regions Y T U :=
  Regions.refresh_to_level Y P L level G.scratchRoom.le G.fit G.slots.le G.capacity (Or.inl G.apart)

/-- Natural intervals of all live source and destination cells, in the
form used by the native copy worker's event footprint. -/
theorem source (x : ℕ) (hx : ColumnCell Y T x) : P.next ≤ x ∧ x < P.stop := by
  obtain ⟨c, lo, hi⟩ := hx
  rw [G.sourceHead c] at lo
  exact ⟨(Nat.le_add_right ..).trans lo, hi.trans_le (G.source_end c)⟩

theorem destination (x : ℕ) (hx : ColumnCell Y U x) :
    incidenceStart L level ≤ x ∧ x < incidenceStart L level + 6*N := by
  obtain ⟨c, lo, hi⟩ := hx
  rw [G.destinationHead c] at lo
  exact ⟨(Nat.le_add_right ..).trans lo, hi.trans_le (G.destination_end c)⟩

theorem sourceAbove (x : ℕ) (hx : ColumnCell Y T x) : levelStart L 0 ≤ x :=
  G.lower.trans (G.source x hx).1

theorem destinationAbove (x : ℕ) (hx : ColumnCell Y U x) : levelStart L 0 ≤ x :=
  (levelStart_mono L (Nat.zero_le level.val)).trans
    ((Nat.le_add_right ..).trans (G.destination x hx).1)

end Packed

variable {a g a₀ dH w : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a + g)) (E : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀) (choice : DyadicRefreshChoice X E hdH conn F)

local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice

theorem base_count : Fintype.card (Y).Base = Fintype.card X.Base * 2^a := by
  change Fintype.card (X.Base × Fin (2^a)) = _
  simp

theorem slot_count (ties stride start : ℕ) :
    (Y).positions * 2^a₀ = (Allocation.plan X a₀ dH ties stride start).capacity := by
  rw [State.positions, Fintype.card_prod, base_count X E hdH conn F hD hd choice,
    Fintype.card_congr (bitWordFinEquiv g), Fintype.card_fin]
  rfl

variable (ties stride : ℕ) (L : Layout) (old : ℕ) (level : Fin L.levels)
local notation "P" => Allocation.plan X a₀ dH ties stride (arrayBase L old)

/-- For the actual branch, the old level's array head locates the scratch
plan above the controller, and the two bounded allocations justify every
source and destination address in the copy. -/
theorem packed (apart : (P).stop ≤ incidenceStart L level) (fit : endAddress L < 2 ^ w)
    (capacity : (Y).positions * 2 ^ a₀ ≤ slotCapacity L) : Packed Y P L level w := by
  refine ⟨slot_count X E hdH conn F hD hd choice ties stride _, capacity, apart, fit, ?_⟩
  have lo := levelStart_mono L (Nat.zero_le old)
  have h : levelStart L old ≤ (P).start := by
    change levelStart L old ≤ arrayBase L old
    unfold arrayBase incidenceStart
    omega
  exact (lo.trans h).trans (by
    simp only [Allocation.Plan.next, Allocation.Plan.reverseSlot, Allocation.Plan.targetPort,
      Allocation.Plan.supply, Allocation.Plan.term, Allocation.Plan.demand]
    omega)

end CompressorRecords.PortRefresh.CopyGeometry

end VPVNP
end Computability
end OAI
