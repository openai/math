import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame

namespace OAI
/-! # Every immutable economic operand remains resident through each native score pass -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing
variable {phases X Y steps w q goods : ℕ}
variable (H : EconomicHeader phases X Y steps)

theorem Resident.move {m out : Memory w} (live : H.Resident m) (ord : H.Ordered)
    (same : ∀x,x<H.stop→ out x=m x) : H.Resident out := by
  apply H.upper_frame ord live _ (fun x _ hi=>same x hi)
  intro i
  apply (live.ports i).frame
  intro x _ hi
  have early:=hi.trans_le (H.ports.end_le i)
  have a : H.scalar.base≤H.scalar.stop:=Nat.le_add_right ..
  have b : H.payload.base≤H.payload.stop:=Nat.le_add_right ..
  have c : H.bought.base≤H.bought.stop:=Nat.le_add_right ..
  have d:=Ordered.menu_bounds H ord
  have e : H.payloadTree.base≤H.payloadTree.stop:=Nat.le_add_right ..
  have f : H.boughtTree.base≤H.stop:=Nat.le_add_right ..
  rcases ord with ⟨o₁,o₂,o₃,o₄,_,o₅,o₆⟩
  exact same x (by omega)

theorem trial (Hord : H.Ordered) (C : Chart w q goods) (m : Memory w) (p h : ℕ) (initial : H.Resident m)
    (whole : mounted C (events C.mesh) m) (hp : p<C.mesh.inject+C.mesh.cool) (hh : h≤C.mesh.outerFuel)
    (floor : ∀e x,x<H.stop→protected C x e) : H.Resident (trialState C m p h) := by
  apply Resident.move H initial Hord
  intro x hx
  rw [trial_as_run]
  exact run_frame C _ _ x (beforeTrial_mounted C m p h whole hp hh) (fun e _=>floor e x hx)

theorem initialScore (Hord : H.Ordered) (C : Chart w q goods) (m : Memory w) (p h : ℕ) (initial : H.Resident m)
    (whole : mounted C (events C.mesh) m) (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel)
    (floor : ∀e x,x<H.stop→protected C x e) : H.Resident (outerScoreMemory C m p h) := by
  apply Resident.move H (H.trial Hord C m p h initial whole hp hh.le floor) Hord
  intro x hx
  let u:=Attempt.outer p h
  let B:=repair C u
  have safe:=floor (.attempt u) x hx
  change B.tests.payload.after (B.tests.excess.after (prepared C u (trialState C m p h))) x=_
  rw [B.tests.payload.frame _ _ safe.2.2.2.1,B.tests.excess.frame _ _ safe.2.2.1,
    prepared_prior C u _ x (outer_head_ready whole hp hh) safe]

theorem replayScore (Hord : H.Ordered) (C : Chart w q goods) (m : Memory w) (p h j b : ℕ) (initial : H.Resident m)
    (whole : mounted C (events C.mesh) m) (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel)
    (hj : j<C.mesh.reserveSteps) (hb : b<C.mesh.innerFuel)
    (floor : ∀e x,x<H.stop→protected C x e) : H.Resident (replayScoreMemory C m p h j b) := by
  apply Resident.move H initial Hord
  intro x hx
  rw [replay_prior C m p h j b x (inner_head_ready whole hp hh hj hb) (floor _ x hx),FeedLayout.inner_as_run]
  exact run_frame C _ _ x (beforeInner_mounted C m p h j b whole hp hh hj hb.le) (fun e _=>floor e x hx)

end Hierarchy.ProtocolRAM.Calendar.StripChart.EconomicHeader
end

end OAI
