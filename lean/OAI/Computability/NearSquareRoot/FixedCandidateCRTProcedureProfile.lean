import OAI.Computability.NearSquareRoot.FixedCandidateCRTJointBudget

/-! # Effective CRT procedures from the native batch profile -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Joint
open IntegerMultiplication Code DigitPacking CandidateParameters EffectiveBoundedTask

noncomputable section

variable (degree : ℕ) (pos : 0 < degree) (rho : Guess → ℝ)
    (h₀ : ∀ p, 0 ≤ rho p) (h₁ : ∀ p, rho p ≤ 1)
    (inv : Bool) (tick arena : Guess → ℕ → ℕ)

/-- The physical batch input consists of the actual seed and the array after
all preceding scatter operations. -/
abbrev BatchFamily : Prop :=
  let f := site degree pos rho h₀ h₁ inv
  Family (fun p (z : Job degree inv p) => tick p (N degree p z.1.1))
    (fun p z => arena p (N degree p z.1.1))
    (fun p z => .fork (send (f p z).actual.seed) (CRTKernel.array Site.actual Site.u Site.f (f p z)))
    (fun p z => CRTKernel.result Site.actual Site.u Site.f (f p z))

variable (kernel : BatchFamily degree pos rho h₀ h₁ inv tick arena)

include kernel in
/-- The compiled sweep implements the source and result arrays specified by
the selector in either CRT direction. -/
theorem sourceOfFamily : SourceRun degree (.crt inv) (peak arena) (clock tick) := by
  have run := effective degree pos rho h₀ h₁ inv tick arena kernel
  cases inv <;> exact run

/-- Assemble the generated CRT command when the native kernel exposes
eventual constant-factor time and space bounds on good reserve guesses. -/
def procedureOfBounds (need : ℕ → ℕ)
    (profile : ∀ p, Enough need p → ProfileAt tick arena (exponent p) p) :
    Procedure degree (.crt inv) :=
  ⟨peak arena,clock tick,sourceOfFamily degree pos rho h₀ h₁ inv tick arena kernel,
    good_of_profileAt tick arena need inv profile⟩

/-- For an exact good-width profile, the batch estimates begin at the
tuple's cutoff and the command executes at every accepted input. -/
def procedureOfProfile (need : ℕ → ℕ) (cut : Guess → ℕ)
    (profile : ∀ p, Enough need p → ∀ n ≥ cut p, arena p n = n ∧
      tick p n = max n (CRTBudget.batchClock (Generator.midExponent (exponent p)) (addressBits n) (CRTBudget.volume n))) :
    Procedure degree (.crt inv) :=
  procedure degree inv tick arena (sourceOfFamily degree pos rho h₀ h₁ inv tick arena kernel) need cut profile

end
end FixedCandidate.CRTStream.Joint

end NearSquareRoot
end Computability
end OAI
