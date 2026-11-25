import OAI.Hierarchy.ProbeDiscrepancyROM
import OAI.Hierarchy.ProbeInstalledReplayStock
import OAI.Hierarchy.ProtocolRAMCalendarScalarROM

namespace OAI
/-! # Both vector-price tables in the common finite boot and actual replay snapshots -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native GlobalTests
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {z d N k phases shapes jobs q goods w D E : ℕ}

theorem master (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (core : Boot.Tape z d) (port : PortROM.Table shapes) (price : ScalarROM.Table phases)
    (outer : Table phases D) (inner : Table phases E) (v : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout v size) (hd : 1≤ d) (first : 2^z≤ b.initial)
    (pages : JointHeader.stop b z N k phases≤ port.base) (heap : heapEnd z d copies≤ port.base)
    (ports : port.stop≤ price.base) (low : price.stop≤ outer.base) (apart : outer.stop≤ inner.base)
    (before : ∀i,inner.stop≤ Boot.low (v i)) (room : inner.stop≤ size)
    (outerFit : outer.entries≤2^wordBits z d copies) (innerFit : inner.entries≤2^wordBits z d copies) :
    let extras:=both outer inner core
    let words:=JointHeader.words b z d N k phase π stock (port.words (price.words extras))
    let m:=Boot.booted v size words
    outer.Resident m ∧ inner.Resident m := by
  dsimp only
  let extras:=both outer inner core
  let words:=JointHeader.words b z d N k phase π stock (port.words (price.words extras))
  let m:=Boot.booted v size words
  obtain ⟨old,new⟩:=resident_both outer inner core apart outerFit innerFit
  have endOuter : outer.base≤ outer.stop := Nat.le_add_right ..
  have endInner : inner.base≤ inner.stop := Nat.le_add_right ..
  have origin (x : ℕ) (firstCell : outer.base≤ x) (lastCell : x< inner.stop) : m x=extras x :=
    JointHeader.tail_origin b phase π stock extras port price v layout hd first pages heap ports x
      (low.trans firstCell) (fun i=>lastCell.trans_le (before i)) (lastCell.trans_le room)
  exact ⟨old.frame (fun x lo hi=>origin x lo ((hi.trans_le apart).trans_le endInner)),
    new.frame (fun x lo hi=>origin x ((endOuter.trans apart).trans lo) hi)⟩

theorem Table.at_replay (t : Table phases D) (C : Chart w q goods) (boot : Memory w) (p h j b : ℕ)
    (start : t.Resident boot) (whole : mounted C (events C.mesh) boot)
    (hp : p< C.mesh.inject+C.mesh.cool) (hh : h< C.mesh.outerFuel) (hj : j< C.mesh.reserveSteps) (hb : b< C.mesh.innerFuel)
    (safe : ∀e x,t.base≤ x→x< t.stop→protected C x e) :
    t.Resident (replayScoreMemory C boot p h j b) := by
  apply start.frame
  intro x lo hi
  rw [replay_prior C boot p h j b x (inner_head_ready whole hp hh hj hb) (safe _ x lo hi),FeedLayout.inner_as_run]
  exact run_frame C _ _ _ (beforeInner_mounted C boot p h j b whole hp hh hj hb.le) (fun e _=>safe e _ lo hi)

theorem purchase_read (F : Type*) [Field F] (depth k : ℕ) [SiteNaming (ChainStrip.Site depth k)]
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (base radix precision p a j b : ℕ) (m : Memory w)
    (hp : p≤ c.inject+c.cool) (hj : j≤ c.reserveSteps) :
    let t:=purchase F depth k base radix precision (DeadlineROM.prices c finish prices)
    let u:=Attempt.inner p a j b
    let s:=deadline c finish prices u
    t.Resident m → t.maxWord<2^w → ∀v,
      (t.bank (DeadlineROM.index c u)).read m ((finFunctionFinEquiv v).val:Word w)=
        (StripDirectory.discrepancyCode (depth:=depth) (k:=k) F s s.M precision radix v:Word w) ∧
      StripDirectory.discrepancyCode (depth:=depth) (k:=k) F s s.M precision radix v<2^w := by
  dsimp only
  intro R fits v
  let u:=Attempt.inner p a j b
  let t:=purchase F depth k base radix precision (DeadlineROM.prices c finish prices)
  rw [←DeadlineROM.inner_price c finish prices p a j b hp hj]
  exact ⟨R (DeadlineROM.index c u) v,(t.word_le (DeadlineROM.index c u) v).trans_lt fits⟩

theorem Table.at_outer (t : Table phases D) (C : Chart w q goods) (boot : Memory w) (p h : ℕ)
    (start : t.Resident boot) (whole : mounted C (events C.mesh) boot)
    (hp : p< C.mesh.inject+C.mesh.cool) (hh : h< C.mesh.outerFuel)
    (safe : ∀e x,t.base≤ x→x< t.stop→protected C x e) :
    t.Resident (outerScoreMemory C boot p h) := by
  apply start.frame
  intro x lo hi
  let u:=Attempt.outer p h
  let B:=repair C u
  have keep:=safe (.attempt u) x lo hi
  have step:=outer_head_ready whole hp hh
  change B.tests.payload.after (B.tests.excess.after (prepared C u (trialState C boot p h))) x=_
  rw [B.tests.payload.frame _ _ keep.2.2.2.1,B.tests.excess.frame _ _ keep.2.2.1,
    prepared_prior C u _ x step keep,trial_as_run]
  exact run_frame C _ _ _ (beforeTrial_mounted C boot p h whole hp hh.le) (fun e _=>safe e _ lo hi)

theorem payload_read (F : Type*) [Field F] (N k : ℕ) [SiteNaming (PayloadStrip.Site N k)]
    (c : Mesh) (finish : ℝ) (prices : PhasePrice) (base radix precision p a : ℕ) (m : Memory w)
    (hp : p≤ c.inject+c.cool) :
    let t:=payload F N k base radix precision (DeadlineROM.prices c finish prices)
    let u:=Attempt.outer p a
    let s:=deadline c finish prices u
    t.Resident m → t.maxWord<2^w → ∀v,
      (t.bank (DeadlineROM.index c u)).read m ((finFunctionFinEquiv v).val:Word w)=
        (StripDirectory.payloadDiscrepancyCode (N:=N) (k:=k) F s precision radix v:Word w) ∧
      StripDirectory.payloadDiscrepancyCode (N:=N) (k:=k) F s precision radix v<2^w := by
  dsimp only
  intro R fits v
  let u:=Attempt.outer p a
  let t:=payload F N k base radix precision (DeadlineROM.prices c finish prices)
  rw [←DeadlineROM.outer_price c finish prices p a hp]
  exact ⟨R (DeadlineROM.index c u) v,(t.word_le (DeadlineROM.index c u) v).trans_lt fits⟩

end Hierarchy.ProtocolRAM.Calendar.DiscrepancyROM
end

end OAI
