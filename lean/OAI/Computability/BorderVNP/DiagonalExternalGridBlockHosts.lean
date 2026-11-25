import OAI.Computability.BorderVNP.DiagonalExternalGridInput
import OAI.Computability.BorderVNP.DiagonalExternalSewPhysical

/-! # Sewing the exterior fields at the retained hosts of the real bottom grids

The original host is determined by the team group and the block ordinal in
the public deck order. A shortening history's retained-site map gives the
final attachment of every port, even when several teams share a bottom box.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.GridHosts

open Cover Crossing Packing Packing.DeckGrid TeamContraction ParseBatch CellEntries
open scoped Classical BigOperators

variable {R r t pins link inner n D : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (q depth : ℕ) (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (groups copies : ℕ) (h : groups*copies = R+1)

/-- Number of original tiles in a bottom deck grid. -/
noncomputable abbrev tileCount (q depth : ℕ) := Fintype.card (Fin q → Deck (depth+2))

/-- Original integral processor block width for a bottom grid. -/
noncomputable abbrev inputBlockWidth (r n q depth : ℕ) := blockWidth (r*n) (tileCount q depth)

/-- The actual parallel array of repeated bottom wired grids with one
copy-sliced word per physical tile. -/
noncomputable abbrev groupedBottom :=
  Network.parallel fun _ : Fin groups =>
    (wiredGrid G q depth order position).groupedRepeat
      (fun _ : Fin (tileCount q depth) => inputBlockWidth r n q depth) order copies

variable (L : Network D (Fin groups × Fin (tileCount q depth)) (fun _ => copies * inputBlockWidth r n q depth))
    (retain : Retains (groupedBottom G q depth order position groups copies) L)

/-- The exterior blocks of a compressed grouped pack are hosted at the images
of their actual bottom grid tiles under the history's retained-site map. -/
noncomputable def blockHosts
    (retain : Retains (groupedBottom G q depth order position groups copies) L) :
    BlockHosts (R := R) (r := r) (w := G.program.length+t) (link := link)
      (FineView.layout L (groupedLane G (tileCount q depth) Fintype.card_pos groups copies h))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (inputBlockWidth r n q depth) := by
  refine ⟨fun z => retain.site ⟨(teamBlocks groups copies h z.1).1,
    baseHost (S := Fin q → Deck (depth+2)) order z.2⟩,?_⟩
  intro p
  change L.attach (groupedLane G (tileCount q depth) Fintype.card_pos groups copies h p).1 = _
  rw [retain.attach]
  have hp : rawBlock (w := G.program.length+t) (link := link) (inputBlockWidth r n q depth) p =
      (p.1,(teamOrdinal p).val / inputBlockWidth r n q depth) := by
    rw [teamOrdinal_val]
    rfl
  rw [hp]
  exact congrArg retain.site (grouped_attach G q depth order position groups copies h p)

/-- Sewing the real exterior intervals of the retained network contracts
each global exterior assignment once in the grouped polynomial tensor. -/
theorem compressed_tensor {Team Param Gadget K : Type*} [Fintype Team] [Fintype Param]
    [CommSemiring K] {b : ℕ} (t0 : Tracked Team Param Gadget b L) (values : Gadget → K)
    (pin : Fin pins → Bool) :
    let lane := groupedLane G (tileCount q depth) Fintype.card_pos groups copies h
    let hosts := blockHosts G q depth order position groups copies h L retain
    ((hosts.bundle.tracked (FineView.tracked L lane t0)).valued values).tensor
      (fun p _ => freeBits G pin p) =
      ∑ ext : Exterior R r link → Bool, (t0.valued values).tensor
        (FineView.extend lane (fun p _ => Prewire.publicBits G p.1 pin ext p.2)) := by
  dsimp only
  exact physical_tracked G (blockHosts G q depth order position groups copies h L retain)
    (FineView.tracked L _ t0) values pin

end Diagonal.ExternalSew.GridHosts

end BorderVNP
end Computability
end OAI
