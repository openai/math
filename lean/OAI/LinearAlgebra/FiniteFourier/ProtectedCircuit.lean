import OAI.LinearAlgebra.FiniteFourier.ProtectedRationals
import OAI.LinearAlgebra.FiniteFourier.DenominatorPrimes
import OAI.LinearAlgebra.FiniteFourier.OpenConvolution.OpenConvolutionBaseChange
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionClear

/-! # Clearing open reductions over protected rationals

The coefficient embedding from the protected ring records the denominator
condition at every gate. An open reduction over that ring can therefore be
converted to an integer multiple with the same shorter convolution calls
and gate counts.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R I O : Type*} [Semiring R] {s n : ℕ} {B : Type*} {len : B → ℕ}

theorem Program.denominatorsIn_mapCoeff (p : Program R I s) (φ : R →+* ℚ)
    (S : Submonoid ℕ) (hφ : ∀ a, (φ a).den ∈ S) :
    (p.mapCoeff φ).DenominatorsIn S := by
  induction p with
  | nil => trivial
  | step p g ih => exact ⟨ih, hφ _, hφ _⟩

theorem Circuit.denominatorsIn_mapCoeff (p : Circuit R I O s) (φ : R →+* ℚ)
    (S : Submonoid ℕ) (hφ : ∀ a, (φ a).den ∈ S) :
    (p.mapCoeff φ).DenominatorsIn S := by
  refine ⟨p.program.denominatorsIn_mapCoeff φ S hφ, ?_⟩
  intro o
  unfold mapCoeff
  dsimp only
  cases h : p.output o with
  | zero => trivial
  | scaled c w => exact hφ c

theorem Circuit.denominatorsIn_protectedRationals {L : Finset ℕ}
    (p : Circuit (protectedRationals L) I O s) :
    (p.mapCoeff (protectedRationals L).subtype).DenominatorsIn (denominatorsAvoiding L) :=
  p.denominatorsIn_mapCoeff _ _ (fun a => a.property)

/-- A protected-ring open formula gives an integer multiple with denominator
support entirely outside the protected primes. -/
theorem OpenConvolution.clearProtected {L : Finset ℕ}
    (p : OpenConvolution (protectedRationals L) n B len) (hp : p.RealizesMultiple 1) :
    ∃ (q : OpenConvolution ℤ n B len) (D : ℕ), 0 < D ∧ D ∈ denominatorsAvoiding L ∧
      q.inputSize = p.inputSize ∧ q.outputSize = p.outputSize ∧ q.RealizesMultiple (D : ℤ) := by
  let φ := (protectedRationals L).subtype
  exact (p.mapCoeff φ).clearDenominators _ p.input.denominatorsIn_protectedRationals
    p.output.denominatorsIn_protectedRationals (by simpa only [map_one] using hp.mapCoeff φ)

end FiniteFourier
end LinearAlgebra
end OAI
