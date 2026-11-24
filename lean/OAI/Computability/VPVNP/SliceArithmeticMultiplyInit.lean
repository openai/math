import OAI.Computability.VPVNP.SliceArithmeticCallPorts
import OAI.Computability.VPVNP.SliceArithmeticCallCopies

/-!
# Initializing the workspace of a slice-field multiplication

The multiplication call starts from empty local stacks. It copies the prime
modulus, zero-word template, polynomial coefficients, multiplier, and degree
markers to their local ports. The query stays on its external stack until the
subsequent digit-order conversion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyCall

open RAMTape BurstRAM HornerControl
open SliceArithmeticStreamRow (state)

/-- Copy the caller's field parameters, multiplier, and degree markers into the initially empty
Horner workspace. -/
def «initialize» : FiniteRoutine Port := CallCopies.copyPlan (localStream .scratch) copies

private theorem validCopies : CallCopies.Valid (localStream .scratch) copies := by
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> simp [copies, localStream, reg, persistent]

/-- The entry routine installs the register bank and the coefficient streams.
Each of the fourteen copies has at most `(e+1)*(w+1)` bits. -/
theorem initialize_runs {p e w : ℕ} [NeZero p] (cb ab bb : List Bool)
    (hc : cb.length = e*w) (hb : bb.length = e*w) :
    ∃ t ≤ 14*(5*((e+1)*(w+1))+2)+1, «initialize».Runs t
      (clean (external p e w cb ab bb))
      (workspace (state (initialRegisters p w) (streams [] [] [] [] (extra cb bb e [] e e)))
        (external p e w cb ab bb)) := by
  let s := clean (external p e w cb ab bb)
  have empty : ∀ q ∈ copies, s q.2 = [] := by
    simp [copies, s, clean, localStream, reg, persistent]
  have bound : ∀ q ∈ copies, (s q.1).length ≤ (e+1)*(w+1) := by
    simp [copies, s, clean, external, hc, hb]
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  obtain ⟨t, ht, run⟩ := CallCopies.copyPlan_runs (localStream .scratch) copies s
    ((e+1)*(w+1)) validCopies rfl empty bound
  refine ⟨t, ht, ?_⟩
  suffices h : CallCopies.copied copies s =
      workspace (state (initialRegisters p w) (streams [] [] [] [] (extra cb bb e [] e e)))
        (external p e w cb ab bb) by rwa [h] at run
  funext i
  rcases i with (i | i) | i
  · cases i with
    | reg i => fin_cases i <;> rfl
    | pub i => exact i.elim0
    | work i => rfl
    | persistent => rfl
    | logPort i => cases i <;> rfl
  · cases i with
    | outer x => cases x <;> rfl
    | _ => rfl
  · rfl

end SliceArithmetic.MultiplyCall

end VPVNP
end Computability
end OAI
