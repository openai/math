import OAI.Hierarchy.DescentResetRegisterBank
import OAI.Hierarchy.DescentMountedExteriorInputs

namespace OAI
/-! # The physical reset node book after count capture and role-table installation -/

namespace Hierarchy.DescentResetNodeBooks

open DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM

/-- When every host occupies one word, its word in any reset page lies between
the scalar output floor and the end of the allocated node book. -/
theorem host_window (floor names nodes hosts groups bits lanes : ℕ) (p : Fin names)
    (h : Fin hosts) (one : chunks groups lanes = 1) :
    floor ≤ (bank floor names nodes hosts groups bits lanes p).base + h.val ∧
    (bank floor names nodes hosts groups bits lanes p).base + h.val <
      endAddress floor names nodes hosts groups bits lanes := by
  let start := output floor names nodes hosts groups bits lanes
  let count := rows hosts groups lanes
  have rowFits : h.val < count := by simpa only [count, rows, one, Nat.mul_one] using h.isLt
  have inside := address_lt start p (⟨h.val, rowFits⟩ : Fin count)
  change start + p.val * count + h.val < start + names * count at inside
  have floor_le : floor ≤ start := Nat.le_add_right _ _
  change floor ≤ start + p.val * count + h.val ∧
    start + p.val * count + h.val < start + names * count + rounded count
  exact ⟨(floor_le.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
    inside.trans_le (Nat.le_add_right _ _)⟩

/-- Count capture and role-table installation preserve the earlier word for
each field, argument, block and host in a one-chunk reset book. -/
theorem header_after_mount (L : DescentDatedPriorOperand.Layout) (floor bits captured size : ℕ)
    (source : ℕ → ℕ) {w roleBase replayBase : ℕ} (mount : RoleMount w roleBase replayBase)
    (m : Memory w) (early : captured + size ≤ floor)
    (done_ : endAddress floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes ≤ roleBase)
    (one : chunks L.groups L.lanes = 1) (f : Fin 7) (j : Fin L.operands)
    (x : Fin L.blocks) (h : Fin L.hosts) :
    mount.phase.image (DescentLowCountBook.output captured source m size)
      ((bank floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes
        (finProdFinEquiv (DescentOperandStateBanks.page f j, x))).base + h.val) =
      m ((previousBank L
        (output floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes) x
        (DescentOperandStateBanks.page f j)).base + h.val) := by
  rw [previous_bank]
  obtain ⟨lower, upper⟩ := host_window floor _ L.nodes L.hosts L.groups bits L.lanes
    (finProdFinEquiv (DescentOperandStateBanks.page f j, x)) h one
  exact mount.between_counts_and_tables captured size source m (early.trans lower) (upper.trans_le done_)

end Hierarchy.DescentResetNodeBooks

end OAI
