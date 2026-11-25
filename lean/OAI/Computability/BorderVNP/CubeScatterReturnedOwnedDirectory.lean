import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleInverse

/-! # The exact rank-indexed lookup column of the recovered physical assignment -/

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

/-- Actual installed scanner input of the one recovered assignment, on the real handoff state. -/
theorem SharedWriters.owned_setup (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1)) :
    PhysicalSetup (l := F.layout ar Fin.valEmbedding decl u)
      (bankData q.2 ar.header.packetBase ar.singleBank) (Fin.valEmbedding ∘ owners q.1) ar.powerBase ar.vertexBase
      ar.publicBase (ar.header.header+13) (ar.header.header+13+ar.header.entries) decl.2 (F.pub u) (F.input u) := by
  obtain ⟨_,installed⟩ := handoff.install u
  obtain ⟨words,views⟩ := writer.replayInputs_after_install ar decl group symbols u template id count
    handoff.banks handoff.spacing (handoff.room u) (handoff.table u) (handoff.frame u) (handoff.source u)
    (handoff.fits u) (handoff.fields u) installed
  have room : ar.ReplayRoom w (readings (F.pub u) 0) := handoff.pub u ▸ handoff.room u
  exact ar.replaySetup owners Fin.valEmbedding q u (F.pub u) (F.input u) decl (f.receivedRows g group)
    receipt.observed.1 receipt.observed.2.1 room
    (by simpa only [handoff.pub,receipt.allocation,Function.comp_def,Fin.valEmbedding,Function.Embedding.coeFn_mk] using words)
    (by simpa only [handoff.pub,receipt.allocation,Function.comp_def,Fin.valEmbedding,Function.Embedding.coeFn_mk] using views)

/-- All real returned lookup triples, including their compact chronological ranks,
name the one recovered assignment. Its physically owned singleton and vertex words
and the entire higher constant deck reside in the same returned memory. -/
theorem SharedWriters.owned_readback (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1)) :
    CubeTriple.Readback (l := F.layout ar Fin.valEmbedding decl u)
      (bankData q.2 ar.header.packetBase ar.singleBank) (Fin.valEmbedding ∘ owners q.1)
      ar.powerBase ar.vertexBase ar.publicBase (F.input u) (F.output u) := by
  have setup := writer.owned_setup symbols handoff receipt u
  obtain ⟨_,_,column⟩ := CubeTriple.native_return setup (F.path u)
  exact ⟨column.count,column.pointer,column.triples,(receipt.recovered.completion u).views,column.sourceWords,column.above⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
