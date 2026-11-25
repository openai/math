import OAI.Hierarchy.ProtocolRAMCalendarArchive
import OAI.Hierarchy.ProtocolRAMCalendarMount

namespace OAI
/-! # The mode-word archive from one mounted RAM image and public address separation -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage
variable {w q d : ℕ} {C : Chart w q d} {mem : Memory w}

def modeAddressSafe (C : Chart w q d) (a : Attempt) (events : List Event) : Prop :=
  ∀ e∈events, protected C (C.modeAt a) e

/-- These conditions depend only on the public chart of addresses. Actual
eligibility of every prefix is obtained from the single mounted full program. -/
structure ModeLifetimes (C : Chart w q d) : Prop where
  wide : 4≤2^w
  outerFuel : 0<C.mesh.outerFuel
  innerFuel : 0<C.mesh.innerFuel
  outerHead : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel,
    let a := Attempt.outer p h
    stopRoom C a ∧ Board (C.layout a) (repair C a) w ∧ 0<(C.layout a).candidates
  innerHead : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel,
    let a := Attempt.inner p h j b
    stopRoom C a ∧ Board (C.layout a) (repair C a) w ∧ 0<(C.layout a).candidates
  trials : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h e, h+1+e<C.mesh.outerFuel →
    modeAddressSafe C (.outer p h) (trialTail C.mesh p h e)
  phases : ∀ p e, p+1+e<C.mesh.inject+C.mesh.cool → ∀ b<C.mesh.outerFuel,
    let h := C.mesh.outerFuel-1
    modeAddressSafe C (.outer p h) (phaseTail C.mesh p h e b)
  bought : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel,
    modeAddressSafe C (.outer p h) (purchaseTail C.mesh p h j b)
  innerTrials : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b e,
    b+1+e<C.mesh.innerFuel → modeAddressSafe C (.inner p h j b) (innerTail p h j b e)
  slices : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j e, j+1+e<C.mesh.reserveSteps →
    ∀ b<C.mesh.innerFuel, let a := C.mesh.innerFuel-1
    modeAddressSafe C (.inner p h j a) (reserveTail C.mesh p h j a e b)

theorem ModeLifetimes.archive (layout : ModeLifetimes C) (whole : mounted C (events C.mesh) mem) :
    ArchiveRoom C mem (C.mesh.inject+C.mesh.cool) where
  wide := layout.wide
  outerFuel := layout.outerFuel
  innerFuel := layout.innerFuel
  outerHead := fun p hp h hh => ⟨outer_head_ready whole hp hh,layout.outerHead p hp h hh⟩
  innerHead := fun p hp h hh j hj b hb => ⟨inner_head_ready whole hp hh hj hb,layout.innerHead p hp h hh j hj b hb⟩
  trials := fun p hp h e he => ⟨trialTail_mounted whole hp he.le,layout.trials p hp h e he⟩
  phases := fun p e he b hb => ⟨phaseTail_mounted whole he (Nat.sub_lt layout.outerFuel (by decide)) hb.le,
    layout.phases p e he b hb⟩
  bought := fun p hp h hh j hj b hb => ⟨purchaseTail_mounted whole hp hh hj hb.le,layout.bought p hp h hh j hj b hb⟩
  innerTrials := fun p hp h hh j hj b e he =>
    ⟨innerTail_mounted whole hp hh hj he.le,layout.innerTrials p hp h hh j hj b e he⟩
  slices := fun p hp h hh j e he b hb =>
    ⟨reserveTail_mounted whole hp hh he (Nat.sub_lt layout.innerFuel (by decide)) hb.le,
      layout.slices p hp h hh j e he b hb⟩

end Hierarchy.ProtocolRAM.Calendar

end OAI
