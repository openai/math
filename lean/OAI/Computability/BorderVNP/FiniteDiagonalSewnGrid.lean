import OAI.Computability.BorderVNP.FiniteCandidateSewHosts
import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical
import OAI.Computability.BorderVNP.DiagonalExternalGridInput
import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawGrid

/-! # The scalar contraction on the actually sewn enriched terminal history

The stored partner-field intervals are real cables of each terminal.
The only supplied lanes of the final tensor are the literal and pin fields.
This sums the original exterior variables exactly once and then opens all
ordinary cube packet and private work indices on that sewn network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch FiniteDiagonal
open scoped BigOperators Classical BorderVNP.Epoch.Cube

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 800000

universe u

variable {D m start T : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (volume : ℕ)
    (installed : bottom.val.pack.layout = (FinitePrewire.fieldGrid G axes gridDepth order position volume).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)

/-- Literal, pin, and shared exterior bits supplied to every bottom-grid
lane of the flattened pack, before connecting the original exterior intervals. -/
noncomputable def fieldGridInputs (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :=
  FineView.extend (GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos
    ((fan S)^T) copies count) (fun p _ => Prewire.publicBits G p.1 pin ext p.2)

/-- The scalar table at an actual terminal with all original exterior
intervals made into internal cables and the free leaves grouped at their
retained physical grid hosts. -/
noncomputable def sewnFieldTable (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : (packHistory bottom M.epoch T).Index) :
    (fieldSewnLayout G axes gridDepth order position count M bottom volume installed q).Tables K :=
  let H := packHistory bottom M.epoch T
  let N := flattenPack T (H.term q).val.pack
  let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos
    ((fan S)^T) copies count
  let hosts := fieldBlockHosts G axes gridDepth order position count M bottom volume installed q
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  hosts.bundle.layout.externalTables (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hg room) hosts.groupOwner
    (hosts.groupAligned hg room) (hosts.bundle.tables (FineView.tables N.layout lane N.table))

/-- One true sewn terminal accounts for all original physical exterior wires
on its actual flattened pack, on the delivered original literal fields. -/
theorem sewnField_value (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : (packHistory bottom M.epoch T).Index) (pin : Fin pins → Bool)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
      GridHosts.inputBlockWidth r n axes gridDepth))
    (delivered : ∀ p, let a := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) p
      bank a.1 a.2 = freeBits G pin p) :
    (fieldSewnLayout G axes gridDepth order position count M bottom volume installed q).value
        (sewnFieldTable G axes gridDepth order position count M bottom volume installed hg q) bank =
      ∑ ext : Exterior R r link → Bool,
        (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).tensor
          (fieldGridInputs G axes gridDepth count pin ext) := by
  let hosts := fieldBlockHosts G axes gridDepth order position count M bottom volume installed q
  let room := GridHosts.gridRoom G (show 0 < GridHosts.tileCount axes gridDepth from Fintype.card_pos)
  let N := flattenPack T ((packHistory bottom M.epoch T).term q).val.pack
  let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos
    ((fan S)^T) copies count
  let t₁ := FineView.tables N.layout lane N.table
  have read : Network.readExternal _ (freeLane hg room) bank = fun p _ => freeBits G pin p :=
    funext fun p => funext fun _ => delivered p
  have group := hosts.bundle.layout.value_packExternal (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
    GridHosts.inputBlockWidth r n axes gridDepth) (freeLane hg room) hosts.groupOwner
    (hosts.groupAligned hg room) (hosts.bundle.tables t₁) bank
  rw [read] at group
  refine (group.trans (physical_value G hosts t₁ pin)).trans ?_
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  exact FineView.value N.layout lane N.table _

/-- The actual adaptive machine's selected scalar tensors after exterior sewing
sum to the proposed prewired batch on every exterior assignment. -/
theorem sum_field_sewn (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth) (pin : Fin pins → Bool)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
      GridHosts.inputBlockWidth r n axes gridDepth))
    (delivered : ∀ p, let a := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) p
      bank a.1 a.2 = freeBits G pin p) :
    (∑ ext : Exterior R r link → Bool,
      (parallelPacks (fun _ : Fin ((fan S)^T) => bottom.val.pack)).tensor
        (fieldGridInputs G axes gridDepth count pin ext)) =
    ∑ q : (packHistory bottom M.epoch T).Index,
      (fieldSewnLayout G axes gridDepth order position count M bottom volume installed q).value
        (sewnFieldTable G axes gridDepth order position count M bottom volume installed hg q) bank := by
  simp_rw [sewnField_value G axes gridDepth order position count M bottom volume installed hg _ pin bank delivered]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro ext _
  exact M.repeated_tensor bottom T le_rfl (fieldGridInputs G axes gridDepth count pin ext)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
