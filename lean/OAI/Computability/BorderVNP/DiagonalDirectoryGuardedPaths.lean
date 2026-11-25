import OAI.Computability.BorderVNP.DiagonalNativeCoreDirectory

/-! # Reconstruction inside an addressed private cell directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

variable {D n d blocks b h K s r : ℕ} {P J Param Gadget Hidden : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} (B : CoreDirectory N n d blocks b h K r)

/-- The path guard of the actual addressed slot table, independent of where
the final tally is written. -/
abbrev Passing (table : N.Tables (Entry Param Gadget)) (x : Ports bits) (pos : TableEntry n b h K s → Gadget) :=
  {v : Path N B.cell n d blocks b h K s // pathTag N B.cell B.slot table x (fun _ => pos) v ≠ 0}

variable (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (num : Gadget ↪ ℕ) (hidden : BottomChoices slabs mult ≃ Hidden)
    (table : Hidden → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N B.edgeID B.portID B.programs (table (hidden z)) num
      (carryPred host (birthPredicate slabs mult z)))
    (legal : ∀ x, (B.programs x).birth.Local ∧ (B.programs x).program.Schema ∧ (B.programs x).program.RelativeBoxes)
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget)

/-- Decode from the common named directory without expanding the public
route's gate or label computation. -/
noncomputable def guardedPathEquiv :
    {u : B.Route s × B.Bank // B.Guard x u} ≃ (Σ z : Hidden, B.Passing (table z) x pos) :=
  (pinnedGuardsEquiv N B.cell B.siteID B.edgeID B.portID B.programs B.owners B.slot x B.owner (fun _ => [])).trans
    ((nativeCoreEquiv N B.cell B.siteID B.edgeID B.portID B.programs host slabs mult widths B.owners B.slot x
      num (fun z => table (hidden z)) model B.owner (fun _ => []) B.owner_site (fun i => (legal i).1)
      (fun i => (legal i).2.1) (fun i => (legal i).2.2) (fun _ => pos)).trans
        (Equiv.sigmaCongrLeft (β := fun z => B.Passing (table z) x pos) hidden))

/-- The retained work and physical route read back from one private bank,
with no evaluation of the finite-field reader or of any scalar. -/
def Reads (v : B.Route s × B.Bank) (z : Hidden) (path : Path N B.cell n d blocks b h K s) : Prop :=
  z = hidden (extractBottom N B.cell B.siteID (placedSize N B.programs) B.owners slabs mult
    (fun _ j => retainedLocation N B.programs host slabs mult widths j) v.1.val v.2) ∧
    path = rawPath N B.cell B.edgeID B.programs B.owners v.1.val v.2

/-- The recovered original and cube coordinates are the retained work prefix
and the routed slot/private-wire payload read from the source bank. -/
theorem guardedPathEquiv_reads (v : {u : B.Route s × B.Bank // B.Guard x u}) :
    let out := B.guardedPathEquiv host slabs mult widths num hidden table model legal x pos v
    out.1 = hidden (extractBottom N B.cell B.siteID (placedSize N B.programs) B.owners slabs mult
      (fun _ j => retainedLocation N B.programs host slabs mult widths j) v.val.1.val v.val.2) ∧
    out.2.val = rawPath N B.cell B.edgeID B.programs B.owners v.val.1.val v.val.2 := ⟨rfl,rfl⟩

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI
