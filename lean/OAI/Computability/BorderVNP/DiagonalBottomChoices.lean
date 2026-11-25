import OAI.Computability.BorderVNP.CubePhysicalBottomExtraction
import OAI.Computability.BorderVNP.PackedGridOwnerBank
import OAI.Computability.BorderVNP.DiagonalPhysicalAssignments

/-! # The true original parse-grid hidden choices in the native private bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellAddresses GridPlacement Cover TeamContraction ParseBatch.Prewire
open BorderVNP.Cube.Physical.NativeAssignments BottomReports
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- A leaf and original routed tile name the physical bottom slab inherited
by a final site. Each copy reads all private fine wires in that tile. -/
abbrev OriginalTile (leaves q depth : ℕ) := Fin leaves × (Fin q → Deck (depth+2))

variable {leaves copies rows : ℕ} (edgeID : (W.routedFine position).Edge ↪ Fin rows)
    (slabs : OriginalTile leaves q depth → Slab)
    (widths : ∀ j, (slabs j).guessed = guessedSize (W.routedFine position) (cell position W.route) j.2)

/-- The physical flat guessed prefix of one original tile is the named
wire assignment used by the routed private factor semantics. -/
noncomputable def tileGuesses (j : OriginalTile leaves q depth) :
    (Fin (slabs j).guessed → Bool) ≃ (W.routedFine position).InsideAssignment (cell position W.route) j.2 :=
  ((finCongr (widths j)).arrowCongr (Equiv.refl Bool)).trans
    (guessedWords (W.routedFine position) (cell position W.route) j.2 edgeID)

/-- Bijection from the original slabs extracted by the physical private
machine to exactly the independently conditioned fine bits in every batch.
The copy and tile indices are transposed but every named cable remains
at its genuine sparse row and within-word position. -/
noncomputable def bottomChoicesEquiv :
    BottomChoices slabs (fun _ => copies) ≃ (Fin leaves → Fin copies → W.Hidden position) where
  toFun z leaf copy tile := W.tileGuesses position edgeID slabs widths (leaf,tile) (z (leaf,tile) copy)
  invFun z j copy := (W.tileGuesses position edgeID slabs widths j).symm (z j.1 copy j.2)
  left_inv z := by funext j copy; exact (W.tileGuesses position edgeID slabs widths j).symm_apply_apply _
  right_inv z := by funext leaf copy tile; exact (W.tileGuesses position edgeID slabs widths _).apply_symm_apply _

/-- Reading back an original cell's private cable directly from the raw bank,
after cast of the declared guessed width. -/
theorem bottomChoicesEquiv_read (z : BottomChoices slabs (fun _ => copies))
    (leaf : Fin leaves) (copy : Fin copies) (tile : Fin q → Deck (depth+2)) :
    W.bottomChoicesEquiv position edgeID slabs widths z leaf copy tile =
      guessedWords (W.routedFine position) (cell position W.route) tile edgeID
        (fun j => z (leaf,tile) copy (Fin.cast (widths (leaf,tile)).symm j)) := rfl

end Packing.DeckGrid.WiredWitness

namespace Diagonal.CellEntries.PacketPlacement

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical

variable {D cn cd cb ch cK cs exp : ℕ} {Team Param Gadget Hidden Native : Type}
    [Fintype Team] [Fintype Param] {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (packet : PacketPlacement Team cn cd cb ch cK N) (tags : Hidden → Tracked Team Param Gadget exp N)
    (bank : Ports bits) (pos : TableEntry cn cb ch cK cs → Gadget)
    (decode : Native ≃ Hidden × Physical.Path N packet.cell cn cd packet.blocks cb ch cK cs)

/-- Filter exactly the real local tagged zero-one and padding guards after
reconstructing the original hidden assignments and final cube payloads.
The resulting fiber is the one inside the public row's Assigned.Path. -/
noncomputable def passingEquiv :
    {u : Native // pathTag N packet.cell packet.slot (tags (decode u).1).tags bank (fun _ => pos) (decode u).2 ≠ 0} ≃
      (Σ z : Hidden, packet.Passing (tags z) bank pos) := by
  let test := fun (x : Hidden × Physical.Path N packet.cell cn cd packet.blocks cb ch cK cs) =>
    pathTag N packet.cell packet.slot (tags x.1).tags bank (fun _ => pos) x.2 ≠ 0
  let fiber : {x // test x} ≃ (Σ z : Hidden, packet.Passing (tags z) bank pos) :=
    { toFun := fun x => ⟨x.val.1,x.val.2,x.property⟩
      invFun := fun v => ⟨(v.1,v.2.val),v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.subtypeEquivOfSubtype (p := test) decode).trans fiber

end Diagonal.CellEntries.PacketPlacement

end BorderVNP
end Computability
end OAI
