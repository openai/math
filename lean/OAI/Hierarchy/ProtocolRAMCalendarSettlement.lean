import OAI.Hierarchy.ProtocolRAMNativeReserveFrame
import OAI.Hierarchy.ProtocolRAMSinkData
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Closing the chronological controller after the prescribed-route settlement -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe
open scoped Fin.CommRing Classical
noncomputable section

variable {w q d r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

def complete (C : Chart w q d) (flag : ℕ) (f : Sink r edges) :=
  (checked C flag).seq (f.native w)

theorem complete_cheap (C : Chart w q d) (flag : ℕ) (f : Sink r edges) :
    CheapCode (complete C flag f) :=
  @cheap_seq w (checked C flag) (f.native w) (@checked_cheap w q d C flag)
    (@RouteSettlement.reporter_cheap w f.source f.table f.destination edges r f.banks f.owners f.geometry)

omit [Fintype I] [Fintype J] in
theorem complete_exec (C : Chart w q d) (flag : ℕ) (f : Sink r edges)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory w)
    (ready : mounted C (events C.mesh) m) (fit : (historyFlag C (events C.mesh)).Fits w flag)
    (room : flag+1<2^w) (sink : f.Mounted (checkedOut C flag m) e ci cj) :
    (complete C flag f).Exec m (f.output (checkedOut C flag m) e ci cj) (checkedCost C+f.clock) := by
  apply Procedure.Exec.then (checked_exec C flag m ready fit room)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact f.exec _ e ci cj sink M pc reg pub exit rom data cfg start entry same

omit [Fintype I] [Fintype J] in
theorem complete_run (C : Chart w q d) (flag : ℕ) (f : Sink r edges)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory w) (state : Word w)
    (ready : mounted C (events C.mesh) m) (ord : separated C (events C.mesh))
    (fit : (historyFlag C (events C.mesh)).Fits w flag) (room : flag+1<2^w)
    (sink : f.Mounted (checkedOut C flag m) e ci cj)
    (below : flag<f.banks.width.base ∧ flag<f.table ∧ flag<f.destination) :
    let M := machine (complete C flag f) (flag:Word w)
    let out := f.output (checkedOut C flag m) e ci cj
    ∃ t≤checkedCost C+f.clock+2, ∃ done, advance M.program t (M.program.start state) m=some (done,out) ∧
      M.program.step done=.finish (some (out flag)) ∧ (out flag=0 ↔ admissible C (events C.mesh) m) := by
  dsimp only
  let v := checkedOut C flag m
  let u := f.output v e ci cj
  have exec : (complete C flag f).Exec m u (checkedCost C+f.clock) := by
    intro P R K M pc reg pub exit rom data cfg start entry same
    exact complete_exec C flag f e ci cj m ready fit room sink M pc reg pub exit rom data cfg start entry same
  obtain ⟨t,ht,done,run,halt⟩ := machine_run (complete C flag f) (flag:Word w) state m u _ exec
  rw [Fin.val_cast_of_lt (by omega : flag<2^w)] at halt
  refine ⟨t,ht,done,run,halt,?_⟩
  rw [f.frame v e ci cj flag below.1 below.2.1 below.2.2 sink.sourceRoom]
  exact checked_read C flag m ready ord (by have := sink.wide; omega)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
