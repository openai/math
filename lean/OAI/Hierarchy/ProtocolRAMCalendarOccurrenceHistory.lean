import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceSource
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceROM
import OAI.Hierarchy.ProtocolRAMCalendarHalfBoot

namespace OAI
/-! # Real occurrence-directory reads at a chronological purchase or reserve attempt -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native StockCommit PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {w q goods : ℕ}

theorem Boot.ports_before_purchase (C : Chart w q goods) (arena : Arena) (m : Memory w)
    (h : PortHeader) (p a : ℕ) (whole : mounted C (events C.mesh) m)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (first : h.stop≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e) (boot : h.Loaded m) :
    let x := Attempt.outer p a
    h.Loaded (postOutput (C.layout x) (repair C x) (prepared C x (trialState C m p a))) := by
  intro x
  apply boot.frame
  intro u _ hi
  have low (e : Event) : u<arena.base C.mesh e :=
    (hi.trans_le first).trans_le (Nat.le_add_right ..)
  have prior := postOutput_prior C x (trialState C m p a) u (outer_head_ready whole hp ha) (floor _ _ (low _))
  apply prior.trans
  rw [trial_as_run]
  exact run_frame C _ _ u (beforeTrial_mounted C m p a whole hp ha.le) (fun e _=>floor e _ (low e))

theorem Boot.ports_before_reserve (C : Chart w q goods) (arena : Arena) (m : Memory w)
    (h : PortHeader) (p a j b : ℕ) (whole : mounted C (events C.mesh) m)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (hb : b<C.mesh.innerFuel) (first : h.stop≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e) (boot : h.Loaded m) :
    let x := Attempt.inner p a j b
    h.Loaded (postOutput (C.layout x) (repair C x) (prepared C x (innerState C m p a j b))) := by
  intro x
  apply boot.frame
  intro u _ hi
  have low (e : Event) : u<arena.base C.mesh e :=
    (hi.trans_le first).trans_le (Nat.le_add_right ..)
  have prior := postOutput_prior C x (innerState C m p a j b) u
    (inner_head_ready whole hp ha hj hb) (floor _ _ (low _))
  apply prior.trans
  rw [FeedLayout.inner_as_run]
  exact run_frame C _ _ u (beforeInner_mounted C m p a j b whole hp ha hj hb.le)
    (fun e _=>floor e _ (low e))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
