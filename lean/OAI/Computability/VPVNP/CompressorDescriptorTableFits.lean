import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorRecordRefreshAllocation

/-!
# Packed suballocations of the descriptor tables

Fixed fields per initial position suffice for all the subarrays of one degree refresh.
The bound includes all segment scratch columns, demands, strided terms, supplies,
expander ROM columns and the six output incidence columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorSpace

open Compression PortRefresh.Allocation

variable (L : Layout)

/-- Any packed suballocation with a fixed linear bound on its length fits this table. -/
theorem tableFits {K amount : ℕ} (h : amount ≤ K*L.positions+K) (pos : 0 < L.positions)
    (capacity : 2*K ≤ L.shape.slots*L.shape.fields) : amount ≤ tableWords L := by
  have k : K ≤ K*L.positions := Nat.le_mul_of_pos_right _ pos
  change amount ≤ L.positions*L.shape.slots*L.shape.fields
  rw [Nat.mul_assoc]
  exact (by rw [Nat.mul_assoc]; omega : amount ≤ (2*K)*L.positions).trans
    ((Nat.mul_le_mul_right L.positions capacity).trans_eq (Nat.mul_comm ..))

/-- The exclusive end of a packed suballocation is representable as a word. -/
theorem tableStop_lt {bits amount : ℕ} (level : Fin L.levels) (table : Fin L.shape.tables)
    (bound : amount ≤ tableWords L) (room : endAddress L < 2^bits) :
    tableBase L level.val table + amount < 2^bits :=
  ((Nat.add_le_add_left bound _).trans ((tableEnd_le_nextLevel L _ _).trans
    (levelStart_mono L level.isLt))).trans_lt room

/-- Exact allocation bound per current site of an elementary degree refresh. -/
theorem refresh_plan_bound {a g : ℕ} (X : State a (a+g)) (a₀ dH t stride start : ℕ) :
    let P := plan X a₀ dH t stride start
    P.stop ≤ start + P.sites * (7*2^a + t + stride + 3*dH + 6*2^a₀) := by
  intro P
  have blocks : P.blocks ≤ P.sites := by
    change Fintype.card X.Base * 2^g ≤ Fintype.card X.Base * 2^a * 2^g
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  have ports : P.ports ≤ P.sites := by
    change 2^a ≤ Fintype.card X.Base * 2^a * 2^g
    exact (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))
  have ht := Nat.mul_le_mul_right t blocks
  have hs := Nat.mul_le_mul_right stride blocks
  have hr := Nat.mul_le_mul_right dH ports
  change start + 7*(P.sites*2^a) + P.blocks*t + P.blocks*stride + P.sites*dH + P.ports*dH + P.ports*dH +
    6*(P.sites*2^a₀) ≤ _
  ring_nf at *
  omega

/-- At a chosen refresh table base, the entire realized pass remains in that level,
and its exclusive end is a word. -/
theorem refresh_table_room {a g w : ℕ} (X : State a (a+g)) (a₀ dH t stride : ℕ)
    (level : Fin L.levels) (table : Fin L.shape.tables)
    (sites : (plan X a₀ dH t stride (tableBase L level table)).sites ≤ L.positions)
    (capacity : 7*2^a+t+stride+3*dH+6*2^a₀ ≤ L.shape.slots*L.shape.fields)
    (room : endAddress L < 2^w) :
    let P := plan X a₀ dH t stride (tableBase L level table)
    P.stop ≤ tableBase L level table + tableWords L ∧ P.stop < 2^w := by
  intro P
  have mul := Nat.mul_le_mul sites capacity
  rw [← Nat.mul_assoc] at mul
  have le := (refresh_plan_bound X a₀ dH t stride (tableBase L level table)).trans (Nat.add_le_add_left mul _)
  exact ⟨le,le.trans_lt (tableStop_lt L level table le_rfl room)⟩

end CompressorRecords.DescriptorSpace

namespace CompressorRecords.DescriptorSpace
open BurstRAM
open scoped Fin.CommRing

/-- The terminal prefix table starts after the final width column, and its final
prefix entry precedes the high header containing the cumulative total word. -/
theorem prefix_bounds (L : Layout) {w : ℕ} (level : Fin L.levels) (table : Fin L.shape.tables)
    (slots H : ℕ) (cap : slots ≤ slotCapacity L) (cells : slots ≤ tableWords L)
    (end_le : endAddress L ≤ H) (room : H+12 < 2^w) :
    ((incidenceBase L level slots 5 : ℕ) : Word w).val+slots ≤ tableBase L level table ∧
      tableBase L level table+slots ≤ H+12 ∧ tableBase L level table+slots < 2^w := by
  have size := Nat.mul_le_mul_left 6 cap
  have low : incidenceBase L level slots 5+slots ≤ tableBase L level table := by
    change incidenceStart L level+5*slots+slots ≤ incidenceStart L level + 6*slotCapacity L + table.val*tableWords L
    omega
  have high : tableBase L level table+slots ≤ H :=
    (Nat.add_le_add_left cells _).trans ((tableEnd_le_nextLevel L _ _).trans ((levelStart_mono L level.isLt).trans end_le))
  rw [Fin.val_natCast,Nat.mod_eq_of_lt (show incidenceBase L level slots 5 < 2^w by omega)]
  exact ⟨low,by omega,by omega⟩

end CompressorRecords.DescriptorSpace

end VPVNP
end Computability
end OAI
