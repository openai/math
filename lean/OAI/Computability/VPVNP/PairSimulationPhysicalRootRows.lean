import OAI.Computability.VPVNP.PairSimulationPhysicalRootGather
import OAI.Computability.VPVNP.PairTerminalPrefixLayout
import OAI.Computability.VPVNP.PairTraversalArena

/-!
# The endpoint directories in the selected traversal arena

The prefix worker publishes the start of every outgoing arc. Its final write
to the role header avoids the six incidence columns. The next stage writes
the descriptor rows and role tags above the selected level's tables, so the
endpoint gather sees the same inverse, width and prefix values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PhysicalScanData

open BurstRAM PrivateRAM Compression CompressorRecords TerminalGatherGeometry
open TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {a g w : ℕ} (X : State a g) (L : TerminalRootGather.Layout)
  (D : DescriptorSpace.Layout) (last : Fin D.levels) (tab : Fin D.shape.tables)

open private transfer_incidence from OAI.Computability.VPVNP.PairTerminalPrefixLayout

/-- The bootstrap of the terminal header preserves the selected state's
packed incidence columns used by the prefix worker. -/
theorem columns_after_bootstrap (A : TerminalBootstrap.Header D last) (limit rad : ℕ)
    (pub : Fin 11 → Word w) (m : Memory w) (ready : TerminalBootstrap.Ready D last A pub m)
    (exp : (pub 7).val = rad) (hr : rad < w) (reserve : 32 ≤ D.base + 2 ^ rad * 2 ^ rad)
    (room : D.base + 2 ^ rad * 2 ^ rad ≤ 2 ^ w)
    (above : DescriptorSpace.endAddress D ≤ TerminalBootstrap.address D.base rad)
    (slots : TerminalPrefix.arcCount X ≤ DescriptorSpace.slotCapacity D)
    (columns : (DescriptorSpace.packedIncidence D w last (TerminalPrefix.arcCount X)).ActualColumns
      X m) :
    (DescriptorSpace.packedIncidence D w last (TerminalPrefix.arcCount X)).ActualColumns X
      (after m (TerminalBootstrap.report D.shape limit pub 0 m).events) := by
  obtain ⟨_, _, _, keep, _⟩ :=
    TerminalBootstrap.native D last A limit pub m 0 ready rad exp hr reserve room
  exact transfer_incidence D last X _ rfl slots above
    (by unfold TerminalBootstrap.address; omega) columns (fun x hx => keep x (.inl hx))

/-- Recover the three gather columns from the complete native prefix run,
including its closing publication in header word 14. -/
theorem prefix_rows (pub : Fin 11 → Word w) (m : Memory w) (rs : List (Report w))
    (end_le : DescriptorSpace.endAddress D ≤ (TerminalLink.header pub).val)
    (room : (TerminalLink.header pub).val + 32 ≤ 2 ^ w)
    (slots : TerminalPrefix.arcCount X ≤ DescriptorSpace.slotCapacity D)
    (cells : TerminalPrefix.arcCount X ≤ DescriptorSpace.tableWords D)
    (inverse : L.incomingHead = DescriptorSpace.incidenceBase D last (TerminalPrefix.arcCount X) 4)
    (widths : L.widthHead = DescriptorSpace.incidenceBase D last (TerminalPrefix.arcCount X) 5)
    (starts : L.prefixHead = DescriptorSpace.tableBase D last tab)
    (columns : (DescriptorSpace.packedIncidence D w last (TerminalPrefix.arcCount X)).ActualColumns
      X m)
    (scan : TerminalPrefix.Segment.Run pub X
      (DescriptorSpace.packedIncidence D w last (TerminalPrefix.arcCount X))
      (DescriptorSpace.tableBase D last tab : Word w) m rs) :
    Rows X L (after m (eventLog rs)) := by
  let H := TerminalLink.header pub
  let n := TerminalPrefix.arcCount X
  let T := DescriptorSpace.packedIncidence D w last n
  have bound := packed_heads D last tab {L with wires := DescriptorSpace.endAddress D} n
    slots cells inverse widths starts le_rfl
  have hi : L.incomingHead + n ≤ DescriptorSpace.endAddress D := bound _ (by simp)
  have hw : L.widthHead + n ≤ DescriptorSpace.endAddress D := bound _ (by simp)
  have hs : L.prefixHead + n ≤ DescriptorSpace.endAddress D := bound _ (by simp)
  have header_at (j : ℕ) (hj : j < 32) : (H + (j : Word w)).val = H.val + j := by
    change (H.val + j % (2 ^ w)) % (2 ^ w) = _
    have small : H.val + j < 2 ^ w := by change (TerminalLink.header pub).val + j < _; omega
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ w), Nat.mod_eq_of_lt small]
  have boundH : DescriptorSpace.endAddress D ≤ H.val := end_le
  have fit : H.val < 2 ^ w := H.isLt
  have port : L.incomingHead = T.actualIn.val := by
    change L.incomingHead = DescriptorSpace.incidenceBase D last n 4 % (2 ^ w)
    rw [← inverse, Nat.mod_eq_of_lt (by omega)]
  have width : L.widthHead = T.width.val := by
    change L.widthHead = DescriptorSpace.incidenceBase D last n 5 % (2 ^ w)
    rw [← widths, Nat.mod_eq_of_lt (by omega)]
  have start : L.prefixHead = ((DescriptorSpace.tableBase D last tab : ℕ) : Word w).val := by
    change L.prefixHead = DescriptorSpace.tableBase D last tab % (2 ^ w)
    rw [← starts, Nat.mod_eq_of_lt (by omega)]
  have before : L.incomingHead + n ≤ L.prefixHead := by
    rw [inverse, starts]
    change DescriptorSpace.incidenceStart D last + 4 * n + n ≤
      DescriptorSpace.incidenceStart D last + 6 * DescriptorSpace.slotCapacity D +
        tab.val * DescriptorSpace.tableWords D
    have h : n ≤ DescriptorSpace.slotCapacity D := slots
    omega
  have sumCell : (H + 12).val = H.val + 12 := header_at 12 (by decide)
  have roleCell : (H + 14).val = H.val + 14 := header_at 14 (by decide)
  have old : T.ActualColumns X
      (writeMemory m (H + 14) (TerminalPrefix.Segment.roleValue pub X m)) :=
    transfer_incidence D last X n rfl slots boundH fit columns (fun x hx => by
      rw [writeMemory, ite_eq_right (by omega)])
  exact rows_of_prefix X L
    ⟨port, width, start, by omega, Or.inr (by change L.incomingHead + n ≤ (H + 12).val; omega),
      Or.inl (by rwa [← start])⟩ old scan.stored

/-- The row and role builders preserve the gather directories below their arena. -/
theorem arena_rows (cap rowBase displacement : ℕ) (roles : List TaggedLayer) (src : Memory w)
    (rows : Rows X L src) (bounds : ∀ h ∈ [L.incomingHead, L.widthHead, L.prefixHead],
      h + TerminalPrefix.arcCount X ≤ rowBase) :
    Rows X L (build cap rowBase rowBase (roles.map TaggedLayer.layer)
      (writeTags displacement cap rowBase roles src)) := by
  apply rows.transfer
  intro h hh i
  have head := bounds h hh
  have hi := i.isLt
  have addr : h + i.val < rowBase := by omega
  rw [build_outside _ _ _ _ _ _ (.inl addr),
    write_tags_outside _ _ _ _ _ _ (.inl (addr.trans_le (Nat.le_add_left _ _)))]

end PairSimulation.PhysicalScanData

end VPVNP
end Computability
end OAI
