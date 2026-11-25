import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledSeed
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstall
import Batteries.Tactic.OpenPrivate

/-! # Broadcasting a measured fence to every head

The auxiliary tape carries a right-end bit at the measured absolute radius.
All heads advance to it, mark it, and rewind. Two mirrored passes then mark
the left boundary on every tape, using distinct input and auxiliary gauges.
The final stationary step removes the temporary origin bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotScaledBroadcast
open IntegerMultiplication TM SlotInstall
open private atHome left second_run from OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstall
variable {A I : Type} [DecidableEq I]

private def copy (aux : I) : Rule (Fence.Symbol A) Bool I :=
  InstallPass.rule (fun _ => true) aux rightEnd atOrigin (fun _ => writeRight)

private theorem broadcast_marks (f : I → ℤ → A) (L : ℕ) (hL : 0<L) (aux : I) :
    InstallPass.mark (fun _ => true) (seed f L aux) L (fun _ => writeRight) =
      paint f L true true (fun _ => false) := by
  funext j p
  by_cases h : p=(L:ℤ)
  · subst p
    simp [InstallPass.mark,InstallPass.gaugePos,seed,paint,writeRight,hL.ne']
  · simp [InstallPass.mark,InstallPass.gaugePos,seed,paint,h]

private theorem copy_run (f : I → ℤ → A) (L : ℕ) (hL : 0<L) (aux : I) :
    let after := paint f L true true (fun _ => false)
    Trace (advance (copy aux)) (base false (seed f L aux)) (2*L+1) (base true after) ∧
      advance (copy aux) (base true after) = none := by
  have h := InstallPass.run (fun _ : I => true) aux rightEnd atOrigin (fun _ => writeRight)
    (seed f L aux) L
  rw [broadcast_marks f L hL] at h
  have r := h (fun k hk => by simp [InstallPass.gaugePos,seed,paint,rightEnd,hk.ne])
    (by simp [InstallPass.gaugePos,seed,paint,rightEnd,hL.ne']) (fun k hk _ => by
      simp [InstallPass.gaugePos,paint,atOrigin,hk.ne']) (by
      simp [InstallPass.gaugePos,paint,atOrigin])
  simpa only [copy,atHome] using r

abbrev PC := Bool ⊕ (Bool ⊕ (Bool ⊕ Bool))

def start : PC := .inl false

def done : PC := .inr (.inr (.inr true))

def rule (inp aux : I) : Rule (Fence.Symbol A) PC I :=
  TapeSequence.rule (copy aux)
    (TapeSequence.rule (left aux) (TapeSequence.rule (left inp) (originRule false) false)
      (.inl false)) (.inl false)

/-- Copy the marked radius to both endpoints of every tape and restore all
heads to zero. The three inter-program transitions are counted. -/
theorem run (inp aux : I) (distinct : inp ≠ aux) (f : I → ℤ → A) (L : ℕ) (hL : 0<L) :
    let last := base done (paint f L false true (fun _ => true))
    Trace (advance (rule inp aux)) (base start (seed f L aux)) (6*L+7) last ∧
      advance (rule inp aux) last = none := by
  let m : I → Bool := fun _ => false
  let a : I → Bool := fun j => decide (j≠aux) || m j
  have all : (fun j => decide (j≠inp) || a j) = (fun _ => true) := by
    funext j
    by_cases eq : j=inp
    · subst j; simp [a,distinct]
    · simp [eq]
  obtain ⟨r,rh⟩ := copy_run f L hL aux
  obtain ⟨l,lh⟩ := second_run aux f L hL m
  obtain ⟨g,gh⟩ := second_run inp f L hL a
  rw [all] at g gh
  have c := origin_run f L hL false true true (fun _ => true)
  have t₃ := TapeSequence.run _ _ false g gh c (origin_halt false _)
  have t₂ := TapeSequence.run _ _ (.inl false) l lh t₃.1 t₃.2
  have t₁ := TapeSequence.run _ _ (.inl false) r rh t₂.1 t₂.2
  rw [show 2*L+1+1+(2*L+1+1+(2*L+1+1+1))=6*L+7 by omega] at t₁
  exact t₁

end Uniform.SlotScaledBroadcast

end NearSquareRoot
end Computability
end OAI
