import OAI.Computability.BorderVNP.CubeScatterOwnedStaticWords

/-! # Actual delivered cell-bank words across the cube installer and owned-group scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

/-- Preserve the word delivered by the returning transmission, at any high
cell-bank address outside the entire fixed cube-constant deck. -/
theorem SharedWriters.owned_delivery_word (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (x : ℕ) (high : ar.publicBase ≤ x)
    (outside : x < ar.stop ∨ CubeConstants.arenaEnd ar.stop id ≤ x) :
    F.output u x = (H u).history.val.2.2 x := by
  refine ((writer.owned_readback symbols handoff receipt u).above x high).trans ?_
  obtain ⟨_,installed⟩ := handoff.install u
  let deck := CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
  let base := CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s
  rcases outside with low | beyond
  · exact TeamHistory.install_before (H u) deck base id (handoff.fits u) (handoff.fields u) installed x low
  · have run := CubeConstants.install_run (H u).pub (H u).macros (H u).history.val.2.1 (H u).history.val.2.2
      deck base id (handoff.fits u) (handoff.fields u)
    have hit := (run.asTest (detOfUnsigned _ (CubeConstants.install_unsigned id).1)).sound installed
    have endIDs : base+(CubeConstants.ids id).length ≤ x := beyond
    have endRecipe : deck.recipes+(CubeConstants.recipes ar.n ar.b ar.h ar.K ar.s).length ≤ x :=
      (Nat.le_add_right base _).trans endIDs
    have after : ar.stop+2 ≤ x := (Nat.le_add_right _ _).trans endRecipe
    exact Fin.ext ((congrFun hit.2 x).trans (CubeConstants.image_outside deck base id _ x
      (by change x ≠ ar.stop; omega) (by change x ≠ ar.stop+1; omega) (.inr endRecipe) (.inr endIDs)))

end TeamContraction

end BorderVNP
end Computability
end OAI
