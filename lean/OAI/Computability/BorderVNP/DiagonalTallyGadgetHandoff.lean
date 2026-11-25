import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback

/-! # Raw gadget IDs on the actual returned route and owned-row history -/

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
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)} (sa : SignedTaskArena.Layout)
variable {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
variable {F : TeamRows.Returns (Fin (R+1)) sa.cube w}
variable {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
  Fin sa.cube.header.d → Fin (R+1)} {template : Frame} {count : ℕ}

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 9000 in
/-- From the original transmission and an actual owned return, recover the complete
raw gadget lookup precondition on the original team's output memory. The installed
words are the fixed position IDs chosen for this shortening identity. -/
theorem SharedWriters.returned_gadget_lookup (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id count F)
    {q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners}
    (receipt : ObservedOwned sa.cube decl group F owners (f.receivedRows g group) q)
    (u : Fin (R+1)) (demand : ℕ) :
    let data := bankData q.2 sa.cube.header.packetBase sa.cube.singleBank
    let numbering := Fin.valEmbedding ∘ owners q.1
    let amount := (CubeVisits.teamList data.axis sa.cube.header.blocks numbering u.val).length
    let lookup := SignedTaskArena.gadgetLookup sa (F.pub u) numbering u.val demand data
    LookupPointers (sa.lookupFrame amount) sa.after.ids (readings (F.pub u) 0) (src u) →
    sa.after.packed ≤ 2^w → amount ≤ sa.p.report.vertices →
    Tally.argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth →
      CubePacket.WordPrepared lookup sa.id (F.pub u) (F.output u) := by
  intro data numbering amount lookup pointers fit capacity width
  let fr := sa.lookupFrame amount
  obtain ⟨deck,initial,tablePtr,idPtr⟩ := writer.owned_word_boot handoff u fr sa.after.ids rfl rfl rfl rfl pointers
  have read := writer.owned_readback symbols handoff receipt u
  have shape : decl=Assignment.Routed.trueDeclaration sa.cube.b sa.cube.s q.1 := receipt.observed.1.symm
  rw [shape] at read
  have cap := CubeAllocation.team_count sa.cube data.axis numbering u.val
  have primary : (F.pub u 0).val+112 ≤ sa.cube.header.header := handoff.pub u ▸ (handoff.room u).primary
  exact SignedTaskArena.wordPrepared_after_owned sa (F.pub u) numbering u.val demand data
    (F.input u) (F.output u) read deck initial tablePtr idPtr rfl cap capacity width primary fit

end TeamContraction

end BorderVNP
end Computability
end OAI
