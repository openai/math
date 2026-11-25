import OAI.Computability.BorderVNP.PackedSewnProgramCharges
import OAI.Computability.BorderVNP.PackedInheritedWorkSignedSewnRoom
import OAI.Computability.BorderVNP.PackedBankFullHistory

/-! # The private sorted cell load on the selected signed exterior wiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch Inherited Inherited.WorkWords PhysicalEpochs CellAddresses
open BorderVNP.Epoch.Round
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000

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
    {np : ℕ} (oldPort : (Fin ((fan S)^T) × Fin (GridHosts.tileCount axes gridDepth)) ↪ Fin np)
    (hp : (fieldSewParams G axes gridDepth).Valid) (q : (packHistory bottom M.epoch T).Index)

local notation "state" => Subtype.val (ProfileSum.term (packHistory bottom (Machine.epoch M) T) q)
local notation "network" => Pack.layout (flattenPack T (EnrichedOuter.State.pack state))
local notation "sewn" => enrichedSewnLayout G axes gridDepth order position count M bottom installed q
local notation "adapt" => enrichedSewnPrograms G axes gridDepth order position count M bottom installed oldPort hp q

local notation "tiles" => GridHosts.tileCount axes gridDepth
local notation "block" => GridHosts.inputBlockWidth r n axes gridDepth

/-- All immutable row words, guard nodes, factor visits, private work and the
new sewn incidences in this region fit in a fixed multiple of the original
pre-sew region. The fixed multiple includes the new interval guards. -/
theorem enrichedSewn_programLoad (short : block ≤ link) (old : Site.Programs network)
    (test : (network).Site → Prop) :
    let pr := adapt old
    localRecords sewn true pr.fullFields.prior pr.fullFields.payload test ≤
      1042*localRecords network true old.fullFields.prior old.fullFields.payload test := by
  intro pr
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
  let lane := GridHosts.groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
  let data : RecordData (state).pack.layout := ⟨old.fullFields.prior,old.fullFields.payload⟩
  have stage := SewnField.sewnPrograms_region network lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state).rows.edge oldPort
    (FieldExport.mergedEdges (fieldSewParams G axes gridDepth) hp (state).rows.edge) finProdFinEquiv.toEmbedding old test
  have geom := enrichedSewn_records G axes gridDepth order position count M bottom installed hp.block short q true data test
  have inc := region_amount_le network old.fullFields.prior old.fullFields.payload (incoming network)
    (fun v => wireCapacity_le network id v _ _) test
  change localRecords sewn true pr.fullFields.prior pr.fullFields.payload test ≤
    localRecords sewn true old.fullFields.prior old.fullFields.payload test+1035*testedWidth (incoming network) test at stage
  change localRecords sewn true old.fullFields.prior old.fullFields.payload test ≤
    7*localRecords network true old.fullFields.prior old.fullFields.payload test at geom
  exact stage.trans ((Nat.add_le_add geom (Nat.mul_le_mul_left 1035 inc)).trans_eq (by ring))

/-- Both pre- and post-expansion local quantities of the selected cell are
charged against the same propagated mass as the actual signed seed. -/
theorem enrichedSewn_programTile {C : Type} (code : (Epoch.Cube D → Deck (depth S start T+1)) ≃ C)
    (rows : ∀ t ht, (M t ht).F.SiteRows) (number : e.Entry → ℕ) (base : Site.Programs bottom.val.pack.layout)
    (B : ℕ) (cap : SiteCap bottom.val.route base.fullFields true B) (short : block ≤ link)
    (c : C) (ex : Bool) :
    let cell := fun v => code (reduceMove (depth S start T) ((state).route.origin v))
    let pr := adapt (M.terminalPrivatePrograms rows number bottom base q)
    localRecords sewn ex pr.fullFields.prior pr.fullFields.payload (fun v => cell v=c) ≤
      1042*(S.publicProgramFactor^T*B) := by
  intro cell pr
  let old := M.terminalPrivatePrograms rows number bottom base q
  have before := M.terminalPrivatePrograms_fullCap rows number bottom base true B cap q
  have tile : localRecords network true old.fullFields.prior old.fullFields.payload (fun v => cell v=c) ≤
      S.publicProgramFactor^T*B := by
    have eq : (fun v : (network).Site => cell v=c) = fun v => reduceMove (depth S start T) ((state).route.origin v)=code.symm c := by
      funext v
      exact propext code.eq_symm_apply.symm
    rw [eq]
    exact (Nat.le_add_left _ 1).trans (before (code.symm c))
  exact (localRecords_le_true sewn ex pr.fullFields.prior pr.fullFields.payload _).trans
    ((enrichedSewn_programLoad G axes gridDepth order position count M bottom installed oldPort hp q short old _).trans
      (Nat.mul_le_mul_left 1042 tile))

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
