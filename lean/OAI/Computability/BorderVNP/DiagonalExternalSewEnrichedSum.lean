import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout
import OAI.Computability.BorderVNP.DiagonalEnrichedTerminal
import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical
import OAI.Computability.BorderVNP.DiagonalPayloadBound

/-! # Exterior sewing on the histories returned by the enriched site machine -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {e : PaidIdentity K D m}
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
    {Team Param Gadget Hidden : Type} [Fintype Team] [Fintype Param] [Fintype Hidden] {exp : ℕ}
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

/-- Enumerate the nested original team owners of the tagged terminal. -/
noncomputable local instance {j : ℕ} : Fintype (Port (fan S) Team j) := Replay.batchFinite (fan S) Team j

/-- The actual tagged terminal after pairing the partner-field intervals at
their retained hosts and grouping the free literal and pin fields. -/
noncomputable def enrichedSewnTerm (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden) :=
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  h.grouped hg (GridHosts.gridRoom G Fintype.card_pos)
    (FineView.tracked L lane (EnrichedOuterReplay.terminal M y hy pos bottom base q z).flat)

omit [Fintype Hidden] in
/-- The partner-wire intervals and grouped free words feed the original
local table at the same retained vertex. Its scalar occurrences therefore
use the payload already charged to that vertex before sewing. -/
theorem enrichedSewn_payloadBound (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden)
    (payload : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site → ℕ)
    (bound : PayloadBound (EnrichedOuterReplay.terminal M y hy pos bottom base q z).flat.tags payload) :
    PayloadBound (enrichedSewnTerm G axes gridDepth order position count M bottom installed
      y hy pos base hg q z).tags payload := by
  let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
  let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
  let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos ((fan S)^T) copies count
  have preserve (tag : Tracked (Port (fan S) Team T) Param Gadget exp L)
      (ht : PayloadBound tag.tags payload) :
      PayloadBound (h.grouped hg (GridHosts.gridRoom G Fintype.card_pos) (FineView.tracked L lane tag)).tags payload :=
    fun v _ _ g => ht v _ _ g
  exact preserve _ bound

/-- Literal, pin and shared wire bits at the actual original grid lanes. -/
noncomputable def enrichedGridInputs (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :=
  FineView.extend (GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos
    ((fan S)^T) copies count) (fun p _ => Prewire.publicBits G p.1 pin ext p.2)

/-- An original processor sees its own ordered public bits at its copy's
actual lane in the bottom grouped word. -/
theorem enrichedGridInputs_read (pin : Fin pins → Bool) (ext : Exterior R r link → Bool)
    (i : Fin ((fan S)^T)) (c : Fin copies) (v : Fin r × Fin (Prewire.publicWidth G)) :
    let N := GridHosts.tileCount axes gridDepth
    let g := GridHosts.inputBlockWidth r n axes gridDepth
    let lane := Network.repeatLane (fun _ : Fin N => g) (GridHosts.wiredLane G N Fintype.card_pos) copies (c,v)
    enrichedGridInputs G axes gridDepth count pin ext (i,lane.1) lane.2 =
      Prewire.publicBits G ((GridHosts.teamBlocks ((fan S)^T) copies count).symm (i,c)) pin ext v :=
  GridHosts.grouped_publicBits G Fintype.card_pos ((fan S)^T) copies count pin ext i c v

set_option maxHeartbeats 2000000 in
/-- Summing the post-sew terms of the complete enriched program computes
the common exterior-wire sum, retaining its actual public branch enumeration
and independent private choices on all original copies. -/
theorem sum_enriched_sewn (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth) (pin : Fin pins → Bool)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
      GridHosts.inputBlockWidth r n axes gridDepth))
    (delivered : ∀ p, let a := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) p
      bank a.1 a.2 = freeBits G pin p) :
    (∑ ext : Exterior R r link → Bool, ∏ i : Fin ((fan S)^T), ∑ z : Hidden,
      ((base z).valued values).tensor (fun p => enrichedGridInputs G axes gridDepth count pin ext (i,p))) =
      ∑ q : (packHistory bottom M.epoch T).Index, ∑ z : Fin ((fan S)^T) → Hidden,
        ((enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hg q z).valued values).tensor bank := by
  let H := packHistory bottom M.epoch T
  let input := enrichedGridInputs G axes gridDepth count pin
  let tag := EnrichedOuterReplay.terminal M y hy pos bottom base
  let term (q : H.Index) (z : Fin ((fan S)^T) → Hidden) (ext : Exterior R r link → Bool) :=
    ((tag q z).flat.valued values).tensor (input ext)
  calc
    _ = ∑ ext, ∑ q : H.Index, ∑ z, term q z ext :=
      Finset.sum_congr rfl fun ext _ => EnrichedOuterReplay.terminal_sum M y hy pos bottom base values lookup (input ext)
    _ = ∑ q : H.Index, ∑ z, ∑ ext, term q z ext := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro z _
      let h := enrichedBlockHosts G axes gridDepth order position count M bottom installed q
      let L := (flattenPack T (H.term q).val.pack).layout
      exact (physical_grouped G h hg (GridHosts.gridRoom G Fintype.card_pos)
        (FineView.tracked L _ (tag q z).flat) values pin bank delivered).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
