import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDirectory
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTraversalLow
import OAI.Computability.BorderVNP.CubeRouteDataLayouts

/-! # Transporting all earlier geometry and public table words to the physical host scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator

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

/-- All source words below the public routing records that are outside the mutable
owned-group arrays survive the actual shared writer, transmission, constant installer,
and owned-group execution. This covers both the low geometric cable directory and the
higher public label, ordinal, pair and receiving-cell directories. -/
theorem SharedWriters.owned_output_static (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (x : ℕ) (before : x < ar.records) (extent : x < ar.header.header+13 ∨ ar.publicBase ≤ x)
    (emitter : x ≠ g.frame+13) (directory : x ≠ readings (F.pub u) 0+46) :
    readings (F.output u) x = src u x := by
  have old : F.output u x = F.input u x := by
    rcases extent with low | high
    · exact CubeTriple.native_return_low (writer.owned_setup symbols handoff receipt u) (F.path u) x low directory
    · exact (writer.owned_readback symbols handoff receipt u).above x high
  have region := ar.writer_order
  have stop : ar.records ≤ ar.stop := (Nat.le_add_right ..).trans (region.2.2.2.2.2.2.1.trans region.2.2.2.2.2.2.2)
  obtain ⟨_,install⟩ := handoff.install u
  have kept := TeamHistory.install_before (H u) (CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s)
    (CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s) id (handoff.fits u) (handoff.fields u) install x (before.trans_le stop)
  exact (congrArg Fin.val old).trans ((congrArg Fin.val kept).trans
    (writer.returned_static ar (readings (H u).pub 0) count (handoff.table u) u x before emitter))

end TeamContraction

end BorderVNP
end Computability
end OAI
