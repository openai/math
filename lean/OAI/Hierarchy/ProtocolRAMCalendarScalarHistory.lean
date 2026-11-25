import OAI.Hierarchy.ProtocolRAMCalendarScalarROM
import OAI.Hierarchy.ProtocolRAMCalendarDeadlineROM
import OAI.Hierarchy.ProtocolRAMCalendarHalfBoot

namespace OAI
/-! # Chronological true scalar prices at both native purchase and reserve score checks -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {w q goods phases : ℕ}

def DeadlineROM.scorePage (c : Mesh) (l : GlobalTests.Layout) (z N k : ℕ) (a : Attempt) :=
  GlobalTests.page l z N k (DeadlineROM.index c a).val

structure ScalarROM.Snapshots (t : ScalarROM.Table phases) (C : Chart w q goods)
    (a : Attempt) (m : Memory w) : Prop where
  entry : t.Resident m
  detector : t.Resident ((guard C a).apply m)
  frozen : t.Resident (prepared C a m)
  tested : t.Resident ((repair C a).tests.after (prepared C a m))
  mask : t.Resident (postSnapshot (C.layout a) (repair C a) (prepared C a m))
  post : t.Resident (postOutput (C.layout a) (repair C a) (prepared C a m))

theorem ScalarROM.snapshots (t : ScalarROM.Table phases) (C : Chart w q goods) (a : Attempt) (m : Memory w)
    (entry : t.Resident m) (readyAt : ready C (.attempt a) m)
    (safe : ∀ x,t.base≤x → x<t.stop → protected C x (.attempt a)) : ScalarROM.Snapshots t C a m := by
  let B := repair C a
  let L := C.layout a
  let v := prepared C a m
  have earlier := entry.frame (fun x lo hi=>prepared_prior C a m x readyAt (safe x lo hi))
  have measured : t.Resident (B.tests.after v) := by
    apply earlier.frame
    intro x lo hi
    obtain ⟨_,_,ex,py,di,_⟩ := safe x lo hi
    change B.tests.discrepancy.after (B.tests.payload.after (B.tests.excess.after v)) x=v x
    rw [B.tests.discrepancy.frame _ _ di,B.tests.payload.frame _ _ py,B.tests.excess.frame _ _ ex]
  refine ⟨entry,entry.frame (fun x lo hi=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (safe x lo hi).1)),
    earlier,measured,?_,entry.frame (fun x lo hi=>postOutput_prior C a m x readyAt (safe x lo hi))⟩
  apply measured.frame
  intro x lo hi
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (safe x lo hi).2.2.2.2.2.1)

theorem Boot.scalar_at_trial (t : ScalarROM.Table phases) (C : Chart w q goods) (arena : Arena)
    (m : Memory w) (p a : ℕ) (boot : t.Resident m) (whole : mounted C (events C.mesh) m)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (first : t.stop≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e) :
    ScalarROM.Snapshots t C (.outer p a) (trialState C m p a) := by
  have safe (x : ℕ) (hi : x<t.stop) (e : Event) := floor e x ((hi.trans_le first).trans_le (Nat.le_add_right ..))
  apply ScalarROM.snapshots t C _ _ _ (outer_head_ready whole hp ha) (fun x _ hi=>safe x hi _)
  rw [trial_as_run]
  exact boot.frame (fun x _ hi=>run_frame C _ _ x (beforeTrial_mounted C m p a whole hp ha.le)
    (fun e _=>safe x hi e))

theorem Boot.scalar_at_inner (t : ScalarROM.Table phases) (C : Chart w q goods) (arena : Arena)
    (m : Memory w) (p a j b : ℕ) (boot : t.Resident m) (whole : mounted C (events C.mesh) m)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (hb : b<C.mesh.innerFuel) (first : t.stop≤arena.first)
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e) :
    ScalarROM.Snapshots t C (.inner p a j b) (innerState C m p a j b) := by
  have safe (x : ℕ) (hi : x<t.stop) (e : Event) := floor e x ((hi.trans_le first).trans_le (Nat.le_add_right ..))
  apply ScalarROM.snapshots t C _ _ _ (inner_head_ready whole hp ha hj hb) (fun x _ hi=>safe x hi _)
  rw [FeedLayout.inner_as_run]
  exact boot.frame (fun x _ hi=>run_frame C _ _ x (beforeInner_mounted C m p a j b whole hp ha hj hb.le)
    (fun e _=>safe x hi e))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
