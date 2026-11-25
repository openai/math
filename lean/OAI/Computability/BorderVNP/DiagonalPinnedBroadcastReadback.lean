import OAI.Computability.BorderVNP.DiagonalSignedPinnedHost
import OAI.Computability.BorderVNP.DiagonalPinnedScheduledBudget

/-! # Recover the exact accepted signed broadcast from its returned writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeArena CubeHeaderInstall
open TeamContraction.JointHeader Transmission DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {slotted : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {widths : I → ℕ}
    (P : SlottedWriter ar D pp lp pins pub slotted base cell id widths)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (raw : Broadcast ar.n ar.header.d ar.header.cap)
    (R X : ℕ)
    (room : SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=slotted) (base:=base)
      f old fresh gates outputs width off ell controls G claims pad raw R X)
local notation3 (prettyPrint := false) "published" => Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)

open private broadcast_of_decoded from OAI.Computability.BorderVNP.DiagonalSignedPinnedHost

include P room in
set_option maxHeartbeats 1200000 in

/-- The returning public checker first proves the Boolean spelling is in
range. Agreement of its decoded numbers with the routed assignment then
determines all bits of the original broadcast. -/
theorem WriterHistory.broadcast_of_pinned_decode {reg doneReg : Bank w} {es : List (TeamRAM.Event w)} {doneMem : Memory w}
    (W : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg published es doneReg doneMem)
    (own : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) own)
    (same : (Fin.ofNat (ar.n+1) (readCode (ar.n+1) raw.1),fun pair j => readCode (ar.header.cap+1) (raw.2 pair j)) =
      Scatter.Assignment.Routed.trueDeclaration ar.b ar.s q.1) :
    (show ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s by rw [room.geometry]; rfl) ▸
      raw=broadcast ar.b ar.s q.1 := by
  obtain ⟨_,_,_,_,_,_,beforeWriter,_⟩ :=
    P.raw_schedule f old fresh gates outputs width off ell controls mac reg G claims pad raw R X room.boot room.geometry
      room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena room.labels room.cells room.teamCount
      room.teamArena room.budget room.million room.scaled room.controlLow room.pointers room.processors room.payload room.fields
      room.rawSpace room.records
  exact broadcast_of_decoded ar own q raw _ (beforeWriter.sound W.prefixRun).1.1 same

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
