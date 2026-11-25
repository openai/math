import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout
import OAI.Computability.BorderVNP.PackedTerminalGroupedHosts

/-! # Signed exterior block hosts on the actual native history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch
open scoped Classical BorderVNP.Epoch.Cube
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
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth) order copies)

/-- The block endpoints in the wire export are exactly the retained original
grid hosts used by the signed terminal contraction. -/
theorem enrichedBlockHosts_attached (q : (packHistory bottom M.epoch T).Index) :
    let L := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
    GridHosts.attachedHosts G Fintype.card_pos count L = enrichedBlockHosts G axes gridDepth order position count M bottom installed q := by
  intro L
  let retained := (Retains.parallel fun _ : Fin ((fan S)^T) => Retains.ofEq installed.symm).trans (enrichedOuterHosts M bottom q)
  have hosts := fun z : Fin (R+1) × ℕ => GridHosts.attached_eq_retained G count order position L retained z.1 z.2
  change ∀ z, (GridHosts.attachedHosts G Fintype.card_pos count L).host z =
    (enrichedBlockHosts G axes gridDepth order position count M bottom installed q).host z at hosts
  cases h₁ : GridHosts.attachedHosts G Fintype.card_pos count L with
  | mk first ok =>
    cases h₂ : enrichedBlockHosts G axes gridDepth order position count M bottom installed q with
    | mk second ok₂ =>
      rw [h₁,h₂] at hosts
      cases funext hosts
      rfl

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
