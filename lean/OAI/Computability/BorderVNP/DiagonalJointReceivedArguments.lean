import OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff
import OAI.Computability.BorderVNP.DiagonalJointSparseInputClock

/-! # Reading the argument scanner directly from the returned joint route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock RoutingISA.Transmission
open RoutingISA.CompactMachine CellMacro.Generator BorderVNP.Cube BorderVNP.Cube.Physical Routing
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride H pins}
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) (a : PinStart.JointPrefix id U)
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count (PinStart.ownedVisits (ar:=ar) U a))

include writer symbols handoff

set_option maxHeartbeats 1200000 in
/-- The scanner's words and its complete pair payloads come from the real
common and local route rows, after the actual constant installation on this
tuple. The full bits of each received tape are available before the owned or
report scans impose further checks. -/
theorem SharedWriters.received_on_joint_prefix (u : Fin (R+1)) :
    let V := PinStart.visits id U (a u)
    let frame := readings (U u).pub 0
    let owner := fun x => (group x).val
    ar.ReplayRoom w frame ∧ ar.ScannerWords frame u.val decl.1.val owner
      (readings (U u).pub) (readings V.constants.val.2.2) decl.2 ∧
      LocalReceived ar frame u.val decl owner V.constants.val.2.2 := by
  intro V frame owner
  obtain ⟨_,run⟩ := handoff.install u
  obtain ⟨words,views⟩ := writer.replayInputs_after_install ar decl group symbols u template id count
    handoff.banks handoff.spacing (handoff.room u) (handoff.table u) (handoff.frame u) (handoff.source u)
    (handoff.fits u) (handoff.fields u) run
  have pub : (U u).pub=(H u).pub := handoff.pub u
  have room : ar.ReplayRoom w frame := by rw [show frame=readings (H u).pub 0 from congrFun (congrArg readings pub) 0]; exact handoff.room u
  rw [←pub] at words views
  refine ⟨room,words,?_⟩
  intro p high localOwner
  exact ⟨f.receivedRows g group p,(writer.declaredRows symbols p).2.2.1,views p high localOwner⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
