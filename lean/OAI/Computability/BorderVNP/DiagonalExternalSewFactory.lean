import OAI.Computability.BorderVNP.DiagonalExternalSewEpoch
import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts
import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical
import OAI.Computability.BorderVNP.PackedSiteEpochs

/-! # Exterior sewing for a physical packing factory

The public factory fixes the exact history index and final layout. Two
properties of its geometry enter this construction: the actual site map
retaining each input attachment, and the sum of its tagged terms over those
same attained histories. Cable order within an epoch can therefore be
chosen by the factory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.PhysicalEpochs Packing.DeckGrid
open CellEntries TeamContraction ParseBatch
open scoped BigOperators Classical

variable {D : ℕ} {K E : Type} [Field K] [Field E] (F : Factory D K)
    {R r t pins link inner n : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ)
    (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {start T copies : ℕ} (deep : F.floor+1+F.drop*T ≤ start) (count : F.fan^T*copies = R+1)
    (bottom : F.State (fun _ : Fin (GridHosts.tileCount axes gridDepth) =>
      copies*GridHosts.inputBlockWidth r n axes gridDepth) start 0)
    (installed : bottom.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)

/-- The retained input vertices in each actual flattened output of the public factory. -/
abbrev FactoryHosts :=
  ∀ q : (F.histories deep bottom T).Index,
    Retains (parallelPacks (fun _ : Fin (F.fan^T) => bottom.pack)).layout
      (flattenPack T ((F.histories deep bottom T).term q).pack).layout

variable (hosts : FactoryHosts F axes gridDepth deep bottom)
    {Team Owners Param Gadget Hidden : Type}
    [Fintype Team] [Fintype Owners] [Fintype Param] [Fintype Hidden] {exp : ℕ}
    (tags : ∀ (q : (F.histories deep bottom T).Index) (_ : Fin (F.fan^T) → Hidden),
      Tracked Owners Param Gadget exp ((F.histories deep bottom T).term q).pack.layout)

/-- The actual grouped network and its private tables for one public history
and one array of private bottom choices. All exterior wires connect the
stored hosts of the original ordered processor fields. -/
noncomputable def factorySewnTerm (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : (F.histories deep bottom T).Index) (z : Fin (F.fan^T) → Hidden) :=
  let L := (flattenPack T ((F.histories deep bottom T).term q).pack).layout
  let retained := (Retains.parallel (fun _ : Fin (F.fan^T) => Retains.ofEq installed.symm)).trans (hosts q)
  let h := GridHosts.blockHosts G axes gridDepth order position (F.fan^T) copies count L retained
  let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos (F.fan^T) copies count
  h.grouped hg (GridHosts.gridRoom G Fintype.card_pos) (FineView.tracked L lane (tags q z).flat)

/-- The physical processor words of this particular grouped exterior assignment. -/
noncomputable def factoryInputs (pin : Fin pins → Bool) (ext : Exterior R r link → Bool) :=
  FineView.extend (GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth)
    Fintype.card_pos (F.fan^T) copies count) (fun p _ => Prewire.publicBits G p.1 pin ext p.2)

/-- Each bottom copy reads the original team and processor at the actual
grid lane under either physical factory. -/
theorem factoryInputs_read (pin : Fin pins → Bool) (ext : Exterior R r link → Bool)
    (i : Fin (F.fan^T)) (c : Fin copies) (v : Fin r × Fin (Prewire.publicWidth G)) :
    let V := GridHosts.tileCount axes gridDepth
    let g := GridHosts.inputBlockWidth r n axes gridDepth
    let lane := Network.repeatLane (fun _ : Fin V => g) (GridHosts.wiredLane G V Fintype.card_pos) copies (c,v)
    factoryInputs F G axes gridDepth count pin ext (i,lane.1) lane.2 =
      Prewire.publicBits G ((GridHosts.teamBlocks (F.fan^T) copies count).symm (i,c)) pin ext v :=
  GridHosts.grouped_publicBits G Fintype.card_pos (F.fan^T) copies count pin ext i c v

set_option maxHeartbeats 2000000 in
/-- A factory's own tagged history expansion remains exact after connecting
the physical shared exterior bits and supplying the delivered literals and
pin. Both sides use the original layout and the same public histograms. -/
theorem sum_factory_sewn (base : Hidden → Tracked Team Param Gadget exp bottom.pack.layout)
    (values : Gadget → E)
    (expansion : ∀ x : Ports (fun _ : Fin (F.fan^T) × Fin (GridHosts.tileCount axes gridDepth) =>
        copies*GridHosts.inputBlockWidth r n axes gridDepth),
      (∏ i, ∑ z : Hidden, ((base z).valued values).tensor (fun p => x (i,p))) =
        ∑ q : (F.histories deep bottom T).Index, ∑ z : Fin (F.fan^T) → Hidden,
          ((tags q z).flat.valued values).tensor x)
    (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth) (pin : Fin pins → Bool)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
      GridHosts.inputBlockWidth r n axes gridDepth))
    (delivered : ∀ p, let a := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) p
      bank a.1 a.2 = freeBits G pin p) :
    (∑ ext : Exterior R r link → Bool, ∏ i : Fin (F.fan^T), ∑ z : Hidden,
      ((base z).valued values).tensor (fun p => factoryInputs F G axes gridDepth count pin ext (i,p))) =
    ∑ q : (F.histories deep bottom T).Index, ∑ z : Fin (F.fan^T) → Hidden,
      ((factorySewnTerm F G axes gridDepth order position deep count bottom installed hosts tags hg q z).valued values).tensor bank := by
  let H := F.histories deep bottom T
  let input := factoryInputs F G axes gridDepth count pin
  let term := fun (q : H.Index) (z : Fin (F.fan^T) → Hidden) (ext : Exterior R r link → Bool) =>
    ((tags q z).flat.valued values).tensor (input ext)
  calc
    _ = ∑ ext, ∑ q : H.Index, ∑ z : Fin (F.fan^T) → Hidden, term q z ext :=
      Finset.sum_congr rfl fun ext _ => expansion (input ext)
    _ = ∑ q : H.Index, ∑ z : Fin (F.fan^T) → Hidden, ∑ ext, term q z ext := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro z _
      let L := (flattenPack T (H.term q).pack).layout
      let retained := (Retains.parallel (fun _ : Fin (F.fan^T) => Retains.ofEq installed.symm)).trans (hosts q)
      let h := GridHosts.blockHosts G axes gridDepth order position (F.fan^T) copies count L retained
      let lane := GridHosts.groupedLane G (GridHosts.tileCount axes gridDepth) Fintype.card_pos (F.fan^T) copies count
      exact (physical_grouped G h hg (GridHosts.gridRoom G Fintype.card_pos)
        (FineView.tracked L lane (tags q z).flat) values pin bank delivered).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
