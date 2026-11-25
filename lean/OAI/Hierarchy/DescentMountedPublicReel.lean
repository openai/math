import OAI.Hierarchy.DescentPublicEarlyReel
import OAI.Hierarchy.DescentLowCountBook
import OAI.Hierarchy.DescentRoleMountSpan

namespace OAI
/-! # Running the count copy, role installation and exterior replay on one memory -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentExteriorMatrixUpdate DescentExteriorShelf ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable (S:AtomSchedule) (k tail roof:ℕ) (tag:ℕ→Bool) (rotation:ℕ→ℕ)
  (j r t e compact:ℕ) {w roleBase:ℕ} (mount:RoleMount w roleBase roof)
  (lo size:ℕ) (source:ℕ→ℕ)

def mountedReplayProgram :=
  ((DescentLowCountBook.program w lo source size).seq mount.phase.program).seq
    (Calendar.earlyProgram S k tail roof tag rotation j r t e compact w)

set_option maxHeartbeats 400000 in
theorem mounted_replay_run (m:Memory w) (bus:0<w) (loRoom:lo<2^w)
    (above:∀i<size,lo+i ≤ source i) (srcRoom:∀i<size,source i+1<2^w)
    (rot:∀i<S.length,rotation i<roof) (earlier:compact+32*span j r t e≤roof)
    (capacity:Calendar.earlyEnd S k tail roof j r t e<2^w) :
    let code:=mountedReplayProgram S k tail roof tag rotation j r t e compact mount lo size source
    let copied:=DescentLowCountBook.output lo source m size
    let step:=mount.phase.image copied
    let output:=Calendar.earlyImage S k tail roof tag rotation j r t e compact step
    code.Exec m output (((4+11*size)+mount.phase.ticks)+Calendar.earlyClock S k tail j r t e) ∧
      CheapCode code ∧
      ∀a,(a<lo ∨ lo+size≤a)→(a<roleBase ∨ Calendar.earlyEnd S k tail roof j r t e≤a) → output a=m a :=by
  intro code copied step output
  have cp : (DescentLowCountBook.program w lo source size).Exec m copied (4+11*size) :=
    DescentLowCountBook.run lo source m size loRoom above srcRoom
  have boot : mount.phase.Runs copied := mount.run copied
  obtain ⟨replayRun, replayHardware, replayFrame⟩ := Calendar.early_run S k tail roof tag rotation j r t e compact step bus rot earlier capacity
  have last_:roof≤Calendar.earlyEnd S k tail roof j r t e:=by
    change roof≤(roof+S.length*Calendar.stride S k tail+S.length+1)+_
    omega
  let prefixCode := DescentLowCountBook.program w lo source size
  let replayCode := Calendar.earlyProgram S k tail roof tag rotation j r t e compact w
  have layout : code = (prefixCode.seq mount.phase.program).seq replayCode := rfl
  rw [layout]
  have prefixCheap : CheapCode prefixCode := (DescentLowCountBook.hardware w lo source size).1
  have mountCheap : CheapCode mount.phase.program := mount.phase.cheap
  have replayCheap : CheapCode replayCode := by
    dsimp only [replayCode]
    exact @replayHardware
  have bothCheap : CheapCode (prefixCode.seq mount.phase.program) :=
    @ProtocolRAM.cheap_seq w prefixCode mount.phase.program (@prefixCheap) (@mountCheap)
  have both : (prefixCode.seq mount.phase.program).Exec m step ((4+11*size)+mount.phase.ticks) := by
    intro labels regs keys machine
    exact Procedure.Exec.then (A:=prefixCode) (B:=mount.phase.program) (a:=m) (b:=copied) (c:=step)
      cp boot machine
  constructor
  · intro labels regs keys machine
    exact Procedure.Exec.then (A:=prefixCode.seq mount.phase.program) (B:=replayCode)
      (a:=m) (b:=step) (c:=output) both replayRun machine
  constructor
  · exact @ProtocolRAM.cheap_seq w (prefixCode.seq mount.phase.program) replayCode (@bothCheap) (@replayCheap)
  · intro a counts slabs
    exact (replayFrame a (slabs.imp_left (fun low=>low.trans_le mount.placed))).trans
      ((mount.frame copied a (slabs.imp_right (fun high=>last_.trans high))).trans
        (DescentLowCountBook.frame lo source m size a counts))

end
end Hierarchy.DescentSixParty.Chronology

end OAI
