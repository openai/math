import OAI.Computability.NearSquareRoot.PrecisionPairProgram
import OAI.Computability.NearSquareRoot.PrecisionPhaseTable
import OAI.Computability.NearSquareRoot.PrecisionPhaseSelection
import OAI.Computability.NearSquareRoot.PrecisionScaledChirp
import OAI.Computability.NearSquareRoot.SynchronizedShortTransform

/-! # Computing the six dilation coefficients of a padded chirp

The setup stack receives a finite word for the normalized Bluestein sum,
generates the fixed order-516 root for the amplitude scale, and computes the
six coefficients of the actual bounded dilation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Grid Strip Staff Carry Dusk Brief Star ShortFourier

/-- Prepare a three-Walsh factorization of the true calibrated multiplier,
starting from the computed Bluestein word at this frequency. -/
theorem prepareDilationFromMultiplier {J : Type} {s : Regime J} {a r p w bits : J → ℕ}
    (ξ : (j : J) → Fin (r j)) (ha : ∀ j, 0 < a j)
    (hp : Realizes s p) (hb : Realizes s bits)
    (b : (j : J) → Grain (w j)) (computed : s.Has (fun j ↦ mark (b j)))
    (happrox : ∀ j, ‖meaning (p j) (w j) (b j) -
      Chirp.bluesteinMultiplier (a j) ((ξ j).val / (r j : ℝ))‖ ≤ 1 / (2 : ℝ) ^ (bits j + 17)) :
    ∃ v : (j : J) → Fin 6 → Grain (bits j + 5),
      s.Has (fun j ↦ List.ofFn fun i ↦ mark (v j i)) ∧
      ∀ j i, ‖meaning (bits j + 2) (bits j + 5) (v j i) -
        dilationTable (calibratedMultiplier (a j) (r j) (ξ j)) i‖ ≤ 1 / (2 : ℝ) ^ bits j := by
  let work j := bits j + 17
  have hw : Realizes s work := hb.plus (.fix 17)
  obtain ⟨rt, hrt, er⟩ := computeAngle work hw (fun _ ↦ 1) (.fixed 1)
    (fun _ ↦ 516) (.natural 516) (fun _ ↦ by decide)
  let input j := scaleByImaginary (grainRat (work j + 2) (rt j)) (grainRat (p j) (b j))
  have hinput : PairRealized s input := scaleByImaginary_realized
    (grainRat_realized (hw.plus (.fix 2)) rt hrt) (grainRat_realized hp b computed)
  have approx j : ‖toComplex (input j) - calibratedMultiplier (a j) (r j) (ξ j)‖ ≤
      1 / (2 : ℝ) ^ (bits j + 11) := by
    apply scaleByImaginary_error
    · apply Chirp.bluesteinMultiplier_bound (ha j)
    · rw [grainRat_value]
      exact happrox j
    · rw [grainRat_value]
      simpa [work, one_div, inv_pow] using er j
  obtain ⟨out, build, close⟩ := computePairTableAt bits hb input hinput
    (fun j ↦ ⟨_, (calibratedMultiplier_lt_half (ha j) (ξ j)).le, approx j⟩)
  exact ⟨out, build, fun j ↦ close j _ (calibratedMultiplier_lt_half (ha j) (ξ j)).le (approx j)⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
