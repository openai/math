import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.CubeScatterTransmissionRouted
import OAI.Computability.BorderVNP.CubeTeamOwnedScheduledWords

/-! # The native team budget on the scheduled RAM of a returned signed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeArena CubeHeaderInstall
open TeamContraction.JointHeader Transmission DiagonalResidueRAM
open private canonicalRead from OAI.Computability.BorderVNP.CubeTeamOwnedScheduledWords

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

include P room in
set_option maxHeartbeats 1200000 in
/-- The actual returning writer has passed the native group checks. They
control every realization of its exact greedy assignment on the same
returned label/interval output, including the one stored by NativeEntry. -/
theorem WriterHistory.pinned_budget_on_return {reg doneReg : Bank w} {es : List (TeamRAM.Event w)} {doneMem : Memory w}
    (W : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg published es doneReg doneMem)
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg published)
    (select : Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h)
    (spells : (show ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s by
      rw [room.geometry]; rfl) ▸ raw = broadcast ar.b ar.s select) :
    let decl := Scatter.Assignment.Routed.trueDeclaration ar.b ar.s select
    let tl := teamLayout ar R
    let prof := powerHeaderImage ar f.dst (readings z.val.2.2)
    ∀ scheduled : ℕ → ℕ, GroupWeights.ScheduleResult (weightLayout ar (pub 0).val decl.1.val) tl prof scheduled →
      (TeamBudget.Layout.mk (R+1) X tl.totals).Passes scheduled := by
  intro decl tl prof scheduled elected
  obtain ⟨tr,mid,selected,chooser,_,_,_,test⟩ :=
    P.raw_schedule f old fresh gates outputs width off ell controls mac reg G claims pad raw R X room.boot room.geometry
      room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena room.labels room.cells room.teamCount
      room.teamArena room.budget room.million room.scaled room.controlLow room.pointers room.processors room.payload room.fields
      room.rawSpace room.records
  obtain ⟨⟨_,_,cap⟩,_⟩ := test.2 W.runs
  obtain rfl : selected=z.val.2.2 := (chooser.unique_of_deterministic (by decide) z.property).2.2
  have shape : ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s := by rw [room.geometry]; rfl
  have axis : decl.1.val=readCode (ar.n+1) raw.1 := (canonicalRead select raw shape spells).1.symm
  apply (elected.passes_iff X).mpr
  rw [axis]
  exact cap

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
