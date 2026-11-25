import OAI.Hierarchy.ProtocolRAMCalendarSegments
import OAI.Hierarchy.ProtocolRAMCalendarModeLaw

namespace OAI
/-! # Authentic mode archives on the actual interval and reserve chronology -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage
noncomputable section
variable {w q d : ℕ} {C : Chart w q d} {mem : Memory w}

def spanRoom (C : Chart w q d) (x : Memory w) (addr : ℕ) (events : List Event) : Prop :=
  mounted C events x ∧ ∀ e∈events, protected C addr e

def headRoom (C : Chart w q d) (a : Attempt) (x : Memory w) : Prop :=
  ready C (.attempt a) x ∧ stopRoom C a ∧ Board (C.layout a) (repair C a) w ∧ 0<(C.layout a).candidates

/-- All hypotheses here concern scheduled memory regions, word width, and the
layout of emitted instructions. Each historical value is recovered by the frame
theorem and its actual earlier write. -/
structure ArchiveRoom (C : Chart w q d) (mem : Memory w) (total : ℕ) : Prop where
  wide : 4≤2^w
  outerFuel : 0<C.mesh.outerFuel
  innerFuel : 0<C.mesh.innerFuel
  outerHead : ∀ p<total, ∀ h<C.mesh.outerFuel,
    headRoom C (.outer p h) (trialState C mem p h)
  innerHead : ∀ p<total, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel,
    headRoom C (.inner p h j b) (innerState C mem p h j b)
  trials : ∀ p<total, ∀ h e, h+1+e<C.mesh.outerFuel →
    spanRoom C (reserveState C mem p h 0) (C.modeAt (.outer p h)) (trialTail C.mesh p h e)
  phases : ∀ p e, p+1+e<total → ∀ b<C.mesh.outerFuel,
    let h := C.mesh.outerFuel-1
    spanRoom C (reserveState C mem p h 0) (C.modeAt (.outer p h)) (phaseTail C.mesh p h e b)
  bought : ∀ p<total, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b<C.mesh.innerFuel,
    spanRoom C (reserveState C mem p h 0) (C.modeAt (.outer p h)) (purchaseTail C.mesh p h j b)
  innerTrials : ∀ p<total, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps, ∀ b e, b+1+e<C.mesh.innerFuel →
    spanRoom C (innerState C mem p h j (b+1)) (C.modeAt (.inner p h j b)) (innerTail p h j b e)
  slices : ∀ p<total, ∀ h<C.mesh.outerFuel, ∀ j e, j+1+e<C.mesh.reserveSteps → ∀ b<C.mesh.innerFuel,
    let a := C.mesh.innerFuel-1
    spanRoom C (innerState C mem p h j (a+1)) (C.modeAt (.inner p h j a))
      (reserveTail C.mesh p h j a e b)

variable {total : ℕ} (R : ArchiveRoom C mem total)
include R

theorem ArchiveRoom.outer_word {p h : ℕ} (hp : p<total) (hh : h<C.mesh.outerFuel) :
    (reserveState C mem p h 0 (C.modeAt (.outer p h))).val=observedMode C mem p h := by
  obtain ⟨fit,_,board,room⟩ := R.outerHead p hp h hh
  have word := observed_mode_word C mem p h ⟨0,room⟩ fit board
  have small := (observedMode_lt C mem p h).trans_le R.wide
  simpa only [Nat.add_zero, Fin.val_cast_of_lt small] using congrArg Fin.val word

theorem ArchiveRoom.inner_word {p h j b : ℕ} (hp : p<total) (hh : h<C.mesh.outerFuel)
    (hj : j<C.mesh.reserveSteps) (hb : b<C.mesh.innerFuel) :
    (innerState C mem p h j (b+1) (C.modeAt (.inner p h j b))).val=observedInnerMode C mem p h j b := by
  obtain ⟨fit,_,board,room⟩ := R.innerHead p hp h hh j hj b hb
  have word := inner_mode_word C mem p h j b ⟨0,room⟩ fit board
  have lt : observedInnerMode C mem p h j b<4 := AttemptGate.actual_lt _ _
  simpa only [Nat.add_zero,Fin.val_cast_of_lt (lt.trans_le R.wide)] using congrArg Fin.val word

theorem ArchiveRoom.outer_agrees {p b : ℕ} (hp : p<total) (hb : b<C.mesh.outerFuel) :
    agrees C.mesh (archive C.modeAt (trialState C mem p b)) (observedHistory C mem) (.outer p b) := by
  constructor
  · intro i hi
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le (show i+1≤p by omega)
    let h := C.mesh.outerFuel-1
    have hf : h<C.mesh.outerFuel := by dsimp [h]; have := R.outerFuel; omega
    have room := R.phases i e (by omega) b hb
    change (trialState C mem p b (C.modeAt (.outer i h))).val = _
    rw [he,phase_archive C mem i h e b _ hf room.1 room.2]
    exact R.outer_word (hi.trans hp) hf
  · intro h hh
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le (show h+1≤b by omega)
    have room := R.trials p hp h e (by omega)
    change (trialState C mem p b (C.modeAt (.outer p h))).val=_
    rw [he,trial_archive C mem p h e _ room.1 room.2]
    exact R.outer_word hp (hh.trans hb)

theorem ArchiveRoom.inner_agrees {p h j b : ℕ} (hp : p<total) (hh : h<C.mesh.outerFuel)
    (hj : j<C.mesh.reserveSteps) (hb : b<C.mesh.innerFuel) :
    agrees C.mesh (archive C.modeAt (innerState C mem p h j b)) (observedHistory C mem) (.inner p h j b) := by
  refine ⟨?_,?_,?_⟩
  · have room := R.bought p hp h hh j hj b hb
    change (innerState C mem p h j b (C.modeAt (.outer p h))).val=_
    rw [purchase_archive C mem p h j b _ room.1 room.2]
    exact R.outer_word hp hh
  · intro i hi
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le (show i+1≤j by omega)
    let a := C.mesh.innerFuel-1
    have ha : a<C.mesh.innerFuel := by dsimp [a]; have := R.innerFuel; omega
    have room := R.slices p hp h hh i e (by omega) b hb
    change (innerState C mem p h j b (C.modeAt (.inner p h i a))).val=_
    rw [he,reserve_archive C mem p h i a e b _ ha room.1 room.2]
    exact R.inner_word hp hh (hi.trans hj) ha
  · intro a ha
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le (show a+1≤b by omega)
    have room := R.innerTrials p hp h hh j hj a e (by omega)
    change (innerState C mem p h j b (C.modeAt (.inner p h j a))).val=_
    rw [he,inner_archive C mem p h j a e _ room.1 room.2]
    exact R.inner_word hp hh hj (ha.trans hb)

theorem ArchiveRoom.outer_law (p : ℕ) (hp : p<total) : outerLaw C.mesh (observedHistory C mem) p :=
  outerLaw_of_snapshot C _ p (trialState C mem p) R.wide fun h hh =>
    ⟨(R.outerHead p hp h hh).1,(R.outerHead p hp h hh).2.1,R.outer_agrees hp hh,rfl⟩

theorem ArchiveRoom.inner_law (p h j : ℕ) (hp : p<total) (hh : h<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps) :
    innerLaw C.mesh (observedHistory C mem) p h j :=
  innerLaw_of_snapshot C _ p h j (innerState C mem p h j) R.wide fun b hb =>
    ⟨(R.innerHead p hp h hh j hj b hb).1,(R.innerHead p hp h hh j hj b hb).2.1,
      R.inner_agrees hp hh hj hb,rfl⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
