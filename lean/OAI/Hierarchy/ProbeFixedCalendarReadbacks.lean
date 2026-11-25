import OAI.Hierarchy.ProbeFixedAcquisition
import OAI.Hierarchy.ProbeFixedOuterFeed

namespace OAI
/-! # Signed outer and replay receipts for the fixed, fully executed calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit PurchaseFrozen
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The original finite, marked stock program supplies every observation used
by the terminal bound, including purchases whose repair fuel runs out. -/
theorem calendar_readbacks :
    ∀ᶠ z : ℕ in Filter.atTop,∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (π : Equiv.Perm (Fin (2^z)))
      (mem fixture : Memory (wordBits z (2^v.W) copies)),
      v.ReadbackRun P z width r banks src tab dst owners π mem fixture →
      let C:=v.nativeChart P z width r banks src tab dst owners
      let A:=v.billedAccount P z width r banks src tab dst owners
      CalendarReadbacks A C mem (2^z) v.mesh.inject v.actualK v.keepLimit v.finish ((dyadicScale v.W)^8)
        ((v.W:ℝ)⁻¹^2) v.loss v.menu.margin (probeDensity k v.W) (purchaseReward k v.W) := by
  filter_upwards [v.repair_word_room,v.purchase_activation,Filter.eventually_ge_atTop v.globalHeight]
    with z wordRoom activate tall
  intro P width r banks src tab dst owners π mem fixture D C A
  have hw:=wordRoom P width D.payload
  let W : RepairWordBounds v P z width:=⟨hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2.1,hw.2.2.2.2.2⟩
  have times (j : ℕ) : j<v.mesh.inject+v.mesh.inject ↔ j<v.mesh.inject+v.mesh.cool := by
    rw [v.clock.same_mesh]
  have room:=v.replay_slice_room P z width D.steps D.digitBudget
  have supply:=v.feed_headroom z width D.payload (by have:=D.dimension;omega)
  have budget : v.keepLimit*width<2^(wordBits z (2^v.W) copies) := by
    exact (Nat.mul_le_mul_right _ (Nat.le_succ v.keepLimit)).trans_lt supply
  have R (j h : ℕ) (hj : j<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) :=
    v.global_source_of_run P z width r banks src tab dst owners mem D.nativeStock D.resident D.prices
      D.precision D.digitBudget tall D.stride j h hj hh
  refine {
    injection:=rfl
    cooling:=v.clock.same_mesh
    outerFuel:=v.clock.outer_pos
    lifetimes:=v.mode_lifetimes P z width r banks src tab dst owners mem D.nativeStock (fun a present=>(D.boards a present).1)
    mounted:=D.nativeStock.mounted_all
    quietTimeline:=v.quiet_timeline P z width r banks src tab dst owners mem fixture D.boards D.nativeStock
      D.positive room D.endFits budget
    idleHead:=fun j hj h hh idle=>v.quiet_head P z width r banks src tab dst owners mem fixture D.boards D.nativeStock
      D.positive j h ((times j).mp hj) hh idle
    failedHead:=fun j hj h hh failed=>D.outer_failed W j h ((times j).mp hj) hh failed
    acquired:=?_
    feed:=fun j hj=>v.outer_feed P z width r banks src tab dst owners mem D.nativeStock room D.endFits supply j ((times j).mp hj)
    scoreRoom:=?_
    payloadWords:=?_
    coolWords:=?_ }
  · intro j hj h hh buy
    have date:=(times j).mp hj
    apply D.acquired W j h date hh buy
    intro u b good
    exact activate P width r banks src tab dst owners mem π ⟨j,date⟩ ⟨h,hh⟩ u b D.nativeStock D.resident D.prices
      D.precision D.digitBudget D.stride D.payload D.geometry D.heap (D.keys j h).1 (D.keys j h).2 D.endFits
      D.archives buy good
  · intro j hj h hh
    obtain ⟨_,cut⟩:=outer_slot C mem j h ((times j).mp hj) hh D.nativeStock.mounted_all
    exact v.score_room P z width r banks src tab dst owners (.outer j h) _ cut.currentReady D.archives.wide
  · intro j hj h hh
    have date : j<v.mesh.inject+v.mesh.cool := hj.trans_le (Nat.le_add_right ..)
    exact ⟨v.payload_vote P z width r banks src tab dst owners mem j h D.precision (R j h date hh) hj.le⟩
  · intro j hj h hh
    have date : v.mesh.inject+j < v.mesh.inject+v.mesh.cool := by
      simpa only [v.clock.same_mesh] using Nat.add_lt_add_left hj v.mesh.inject
    have time : outerTime v.mesh v.finish (v.mesh.inject+j) = clockTime v.finish v.mesh.inject j :=
      (v.phase_clock (v.mesh.inject+j)).trans (by simp only [phaseTime,Nat.add_sub_cancel_left])
    refine ⟨?_⟩
    simpa only [envelope,time] using
      v.cool_vote P z width r banks src tab dst owners mem (v.mesh.inject+j) h D.precision
        (R _ h date hh) date.le

/-- Settled cash and the box price of the retained physical stock after the
last feed, measured on the same memory as every dated readback. -/
theorem calendar_cash :
    ∀ᶠ z : ℕ in Filter.atTop,∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (π : Equiv.Perm (Fin (2^z)))
      (mem fixture : Memory (wordBits z (2^v.W) copies)),
      v.ReadbackRun P z width r banks src tab dst owners π mem fixture →
      let C:=v.nativeChart P z width r banks src tab dst owners
      let A:=v.billedAccount P z width r banks src tab dst owners
      let final:=A.read (.outer (C.mesh.inject+C.mesh.cool) 0) (run C (events C.mesh) mem)
      A.bank.cash final+pairing (A.bank.units width final) A.box≤6*(2^z:ℕ) := by
  filter_upwards [v.calendar_readbacks] with z receipts
  intro P width r banks src tab dst owners π mem fixture D
  exact v.terminal (v.privateArena P z width) (v.nativeFormats P z width) P.joint.initial width
    (v.issued P z width r banks src tab dst owners) (v.nativeChart P z width r banks src tab dst owners) rfl mem
    (fun i=>Fin.ext (D.prices.empty i)) D.widths (receipts P width r banks src tab dst owners π mem fixture D)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
