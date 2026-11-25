import OAI.Computability.BorderVNP.TransmissionPinsLoop
import OAI.Computability.BorderVNP.TransmissionPinsReplay
import OAI.Computability.BorderVNP.TransmissionPinsPositive

/-!
# The exact fixed-length index guess in the native evaluator

Every return is counted once by its prescribed index assignment. The statement includes
zero-width indices, the other teams, the physical memory effect and the uniform runtime.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

/-- Number of real private guesses made by this team. -/
def Layout.guessWidth (L : Layout) := if L.team = 0 then L.width else 0

/-- Extend the true fixed-length assignment by zero on the unused pin positions. -/
def extendGuess {k : ℕ} (b : Fin k → Bool) (x : ℕ) : Bool := if h : x < k then b ⟨x,h⟩ else false

/-- Section 11's substituted-index choices are in bijection with all returns of the
physical native fragment. Each return has positive sign, uses precisely its bit string,
fits the stated clock, and produces the specified copy of the live and substituted pins. -/
theorem preparePins_exact {w : ℕ} (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) (hwidth : L.width ≤ L.count) (fits : LoopFits w L) :
    ∃ E : (Fin L.guessWidth → Bool) ≃ Return pub macros s m, ∀ b,
      (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
      traceCost (E b).val.1 ≤ pinSetup.slots + 17*L.count + 1 ∧
      (∀ e ∈ (E b).val.1, e.sign = .plus) ∧ Ready L L.count (E b).val.2.1 ∧
      (E b).val.2.2 = preparedMemory L (extendGuess b) m L.count := by
  have complete (b : Fin L.guessWidth → Bool) : ∃ z : Return pub macros s m,
      z.val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
      traceCost z.val.1 ≤ pinSetup.slots + 17*L.count + 1 ∧
      (∀ e ∈ z.val.1, e.sign = .plus) ∧ Ready L L.count z.val.2.1 ∧
      z.val.2.2 = preparedMemory L (extendGuess b) m L.count := by
    obtain ⟨es,t,r,ct,bits,hr⟩ := preparePins_run L pub macros m s (extendGuess b) frame hframe
      ht hs hc hwidth fits
    refine ⟨⟨⟨es,t,_⟩,r⟩, ?_, ct, preparePins_positive r, hr, rfl⟩
    change es.flatMap TeamRAM.Event.choices = _
    rw [bits]
    apply congrArg List.ofFn
    funext i
    exact dite_eq_left i.isLt
  choose run effects using complete
  exact ⟨returnEquiv run (fun b => (effects b).1), effects⟩

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
