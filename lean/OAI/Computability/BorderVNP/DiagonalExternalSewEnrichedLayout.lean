import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedOuter
import OAI.Computability.BorderVNP.DiagonalExternalSewGroupedBudget
import OAI.Computability.BorderVNP.PackedEnrichedHistoryRecords

/-! # Exterior cable layout on the histories returned by the enriched site machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch
open BorderVNP.Epoch.Round Packing.PhysicalEpochs
open scoped BigOperators Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

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
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)

/-- The original grid block hosts on the actual routed terminal of this
enriched histogram, before connecting the shared exterior wires. -/
noncomputable def enrichedBlockHosts (q : (packHistory bottom M.epoch T).Index) :=
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let retained := (Retains.parallel fun _ : Fin ((fan S)^T) => Retains.ofEq installed.symm).trans
    (enrichedOuterHosts M bottom q)
  GridHosts.blockHosts G axes gridDepth order position ((fan S)^T) copies count L retained

/-- The sewn physical layout with one grouped word per team and initial tile,
and one cable for each paired interval of its original partner fields. -/
noncomputable abbrev enrichedSewnLayout (q : (packHistory bottom M.epoch T).Index) :
    Network D (FreeBlock R (GridHosts.tileCount axes gridDepth)) (fun _ => GridHosts.inputBlockWidth r n axes gridDepth) :=
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  h.bundle.freeGroups h.groupOwner

/-- The grouped literal and pin word for a team is delivered to the
final routed tile of the corresponding original grid host. -/
theorem enrichedSewn_freeTile (q : (packHistory bottom M.epoch T).Index)
    (a : FreeBlock R (GridHosts.tileCount axes gridDepth)) :
    let state := ((packHistory bottom M.epoch T).term q).val
    reduceMove (depth S start T) (state.route.origin
      ((enrichedSewnLayout G axes gridDepth order position count M bottom installed q).attach a)) =
      enrichedOriginTile M bottom q (GridHosts.teamBlocks ((fan S)^T) copies count a.1).1
        (bottom.val.pack.layout.attach a.2) := by
  let state := ((packHistory bottom M.epoch T).term q).val
  let retained := (Retains.parallel fun _ : Fin ((fan S)^T) => Retains.ofEq installed.symm).trans
    (enrichedOuterHosts M bottom q)
  let L := (flattenPack T state.pack).layout
  have owner := GridHosts.groupOwner_eq G axes gridDepth order position ((fan S)^T) copies count L retained a
  exact (congrArg (fun v => reduceMove (depth S start T) (state.route.origin v)) owner).trans
    (enrichedOriginTile_attach M bottom q _ a.2).symm

/-- The additional cable width across any terminal cell partition is paid
for by the original exterior incidence budget. -/
theorem enrichedSewn_intercell {Cell : Type*} (q : (packHistory bottom M.epoch T).Index)
    (cell : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site → Cell) (X₀ : ℕ)
    (exterior : r*R*link ≤ X₀) :
    intercellWidth (enrichedSewnLayout G axes gridDepth order position count M bottom installed q) cell ≤
      intercellWidth (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout cell + (R+1)*X₀ := by
  let retained := (Retains.parallel fun _ : Fin ((fan S)^T) => Retains.ofEq installed.symm).trans
    (enrichedOuterHosts M bottom q)
  exact GridHosts.grouped_intercell_increment G axes gridDepth order position ((fan S)^T) copies count _ retained
    cell X₀ exterior

/-- Record counts on the actual final hosts pay for all the new physical
exterior endpoints and grouped free words in either counting mode. -/
theorem enrichedSewn_records (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (small : GridHosts.inputBlockWidth r n axes gridDepth ≤ link)
    (q : (packHistory bottom M.epoch T).Index) (expanded : Bool)
    (fields : Epoch.Round.RecordData ((packHistory bottom M.epoch T).term q).val.pack.layout)
    (test : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site → Prop) :
    localRecords (enrichedSewnLayout G axes gridDepth order position count M bottom installed q)
      expanded fields.prior fields.payload test ≤
      (if expanded then 7 else 5*copies) *
        localRecords (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
          expanded fields.prior fields.payload test := by
  let retained := (Retains.parallel fun _ : Fin ((fan S)^T) => Retains.ofEq installed.symm).trans
    (enrichedOuterHosts M bottom q)
  exact GridHosts.grouped_records G axes gridDepth order position ((fan S)^T) copies count _ retained
    hg small expanded fields.prior fields.payload test

/-- Every final routed tile pays for its actual post-sew records from the
initial cap, with the measured schedule factor at each complete epoch. -/
theorem enrichedSewn_historyRecords (base : RecordData bottom.val.pack.layout) (expanded : Bool) (B : ℕ)
    (hbase : SiteCap bottom.val.route base expanded B) (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (small : GridHosts.inputBlockWidth r n axes gridDepth ≤ link) (q : (packHistory bottom M.epoch T).Index)
    (tile : Epoch.Cube D → Deck (depth S start T+1)) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let fields := M.historyFields bottom base T q
    localRecords (enrichedSewnLayout G axes gridDepth order position count M bottom installed q)
      expanded fields.prior fields.payload (fun v => reduceMove (depth S start T) (state.route.origin v) = tile) ≤
        (if expanded then 7 else 5*copies)*(S.recordFactor^T*B) := by
  let state := ((packHistory bottom M.epoch T).term q).val
  let fields := M.historyFields bottom base T q
  let test (v : state.pack.layout.Site) := reduceMove (depth S start T) (state.route.origin v) = tile
  have sew := enrichedSewn_records G axes gridDepth order position count M bottom installed hg small q expanded fields test
  have flat := SiteRoutes.flatten_records state.pack expanded fields.prior fields.payload test
  have cap := M.historyFields_bound bottom base expanded B hbase T q tile
  change 1+localRecords state.pack.layout expanded fields.prior fields.payload test ≤ S.recordFactor^T*B at cap
  exact sew.trans (Nat.mul_le_mul_left _ (flat.le.trans ((Nat.le_add_left _ 1).trans cap)))

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
