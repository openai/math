import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderReplay
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDeck

/-! # The parsed signed claim at the genuine route and owned traversal return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator ProcessorSlots JointHeader SignedTaskArena
open private detOfUnsigned from OAI.Computability.BorderVNP.CubeISALocalRowFrame

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)} (sa : SignedTaskArena.Layout)
variable {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
variable {F : TeamRows.Returns (Fin (R+1)) sa.cube w}
variable {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
  Fin sa.cube.header.d → Fin (R+1)} {template : Frame} {count : ℕ}

set_option maxRecDepth 9000 in
/-- The original parsed header lies below all packet banks. Every genuine route,
fixed table installation and owned traversal preserves each of its physical words
except the two published frame counts. -/
theorem SharedWriters.returned_header_word (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id count F)
    {q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners}
    (receipt : ObservedOwned sa.cube decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (x : ℕ) (lo : x<sa.cube.header.header)
    (shared : x≠(F.pub u 0).val+13) (owned : x≠(F.pub u 0).val+46) :
    readings (F.output u) x=src u x := by
  have setup := writer.owned_setup symbols handoff receipt u
  let frame := CubeConstants.inArena template sa.cube.stop sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s
  let base := CubeConstants.idBase sa.cube.stop sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s
  obtain ⟨_,installed⟩ := handoff.install u
  have install := CubeConstants.install_run (H u).pub (H u).macros (H u).history.val.2.1 (H u).history.val.2.2
    frame base sa.id (handoff.fits u) (handoff.fields u)
  have image := ((install.asTest (detOfUnsigned _ (CubeConstants.install_unsigned sa.id).1)).sound installed).2
  have below : x<sa.cube.stop := by
    obtain ⟨_,_,_,publicBase,pair,cell⟩ := sa.cube.separated
    have primary := sa.cube.group_order.1
    omega
  have kept := ReaderKept.afterOwned_word sa.cube template sa.id image setup (F.path u) x ⟨by omega,below⟩ owned
  have old := writer.returned_static sa.cube (readings (H u).pub 0) count (handoff.table u) u x
    (lo.trans_le (Evaluator.secondary_le_records sa.cube)) (by rw [handoff.frame]; simpa only [handoff.pub,readings] using shared)
  exact (congrArg Fin.val kept).trans old

/-- On the positive branch the original arbitrary parsed claim, the descriptor
pointer and machine width all survive into the recovered owned return. -/
theorem SharedWriters.returned_header_seed {reserve axes groups cap width : ℕ}
    (A : StartupArena) (p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width)
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id count F)
    {q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners}
    (receipt : ObservedOwned sa.cube decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (prior : Memory w) (frame : (F.pub u 0).val=A.frame)
    (size : A.header=PositiveFields.width reserve axes groups cap sa.cube.teams sa.dim width)
    (position : A.next ≤ sa.cube.header.header) :
    let raw := rawAddress A reserve axes groups cap
    HeaderSeed sa p (F.pub u) raw u.val prior →
    (∀ x,headerSeedRead A.frame raw (sa.cube.teams*sa.dim*width) x → src u x=readings prior x) →
    HeaderSeed sa p (F.pub u) raw u.val (F.output u) := by
  intro raw seed before
  apply seed.transfer
  intro x hx
  rw [frame] at hx
  obtain ⟨lower,_,endPins⟩ := rawAddress_room sa A size
  have under := (seedRead_before_pins sa A size hx).trans_le (endPins.trans position)
  exact Fin.ext ((writer.returned_header_word sa symbols handoff receipt u x under
    (frame ▸ headerSeedRead_other hx lower (j:=13) (by decide) (by decide))
    (frame ▸ headerSeedRead_other hx lower (j:=46) (by decide) (by decide))).trans (before x hx))

end TeamContraction

end BorderVNP
end Computability
end OAI
