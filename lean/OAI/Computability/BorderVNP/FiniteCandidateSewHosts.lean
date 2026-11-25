import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout
import OAI.Computability.BorderVNP.FinitePrewireGrid

/-! # Retained exterior-interval hosts for an arbitrary finite-field candidate

The channel padding of the bottom grid uses the volume of the proposed
trivalent network, including its actual prewiring overhead. Its public
input rows and attachment to the retained grid tiles agree with the shared
processor-slot layout independently of that channel capacity.
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


/-- The stored cable endpoints on a genuine selected terminal with the
finite candidate's own original channel capacity. -/
noncomputable def fieldBlockHosts (q : (packHistory bottom M.epoch T).Index) :
    let terminal := (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout
    let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos
      ((fan S)^T) copies count
    BlockHosts (R := R) (r := r) (w := G.program.length+t) (link := link)
      (FineView.layout terminal lane) (Equiv.refl (PublicPort R r (G.program.length+t) link))
      (GridHosts.inputBlockWidth r n axes gridDepth) := by
  intro terminal lane
  let groups := (fan S)^T
  let g := GridHosts.inputBlockWidth r n axes gridDepth
  let ret := (Retains.parallel fun _ : Fin groups => Retains.ofEq installed.symm).trans
    (enrichedOuterHosts M bottom q)
  refine ⟨fun z => ret.site ⟨(GridHosts.teamBlocks groups copies count z.1).1,
    GridHosts.baseHost (S := Fin axes → Deck (gridDepth+2)) order z.2⟩,?_⟩
  intro p
  change terminal.attach (lane p).1 = _
  rw [ret.attach]
  have hp : rawBlock (w := G.program.length+t) (link := link) g p =
      (p.1,(teamOrdinal p).val / g) := by
    rw [teamOrdinal_val]
    rfl
  rw [hp]
  exact congrArg ret.site (GridHosts.grouped_attach G axes gridDepth order position groups copies count p)

/-- The true sewn finite candidate terminal, using its own physical interval hosts. -/
noncomputable abbrev fieldSewnLayout (q : (packHistory bottom M.epoch T).Index) :
    Network D (FreeBlock R (GridHosts.tileCount axes gridDepth)) (fun _ => GridHosts.inputBlockWidth r n axes gridDepth) :=
  let h := fieldBlockHosts G axes gridDepth order position count M bottom volume installed q
  h.bundle.freeGroups h.groupOwner

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
