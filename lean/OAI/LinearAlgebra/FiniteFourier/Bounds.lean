import OAI.LinearAlgebra.FiniteFourier.Asymptotics
import OAI.LinearAlgebra.FiniteFourier.CircuitToFeedback
import OAI.LinearAlgebra.FiniteFourier.DenseLower
import OAI.LinearAlgebra.FiniteFourier.TransferParameters

/-! # The two uniform estimates in the Fourier complexity theorem

The constants are quantified before both the group and the splitting field.
These definitions let the two proof components be stated and checked
independently. The lower estimate uses geometric border of uniquely solvable
feedback systems, and therefore applies to the usual circuit complexity too.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
universe u v

open Filter
open scoped Topology

/-- The uniform upper estimate of Theorem 1.1 for forward transforms. -/
def UniformFourierUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G →
      (complexity (fourierMatrix G K) : ℝ) ≤ C * Fintype.card G *
        (1 + Real.logb 2 (Fintype.card G)) ^ ((1 : ℝ)/2 + ε)

/-- The uniform lower estimate for forward transforms, including feedback border. -/
def UniformFourierBorderLower : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G → ∀ S : ℕ, GeometricBorderAtMost (fourierMatrix G K) S →
      c * Fintype.card G * Real.sqrt (Real.logb 2 (Fintype.card G)) ≤ S

/-- The explicit large-order estimate of Theorem tr:fourier suffices for the
uniform lower estimate, using the unconditional dense-matrix obstruction
for every smaller order. -/
theorem uniformFourierBorderLower_of_large_orders
    (hlarge : ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G → 144 ≤ Real.logb 2 (Fintype.card G) →
      ∀ S : ℕ, GeometricBorderAtMost (fourierMatrix G K) S →
      (2 : ℝ) ^ (-(28 : ℝ)) * Fintype.card G *
        ⌊Real.sqrt (Real.logb 2 (Fintype.card G)) / 6⌋₊ < S) :
    UniformFourierBorderLower.{u,v} := by
  obtain ⟨κ, hκ, hk⟩ := uniform_fourier_sqrt_lower
  refine ⟨κ, hκ, ?_⟩
  intro G K _ _ _ had hN S hb
  have hlinear := (fourier_border_card_le G K had hN S).1 hb
  exact hk _ S hN (by omega) (fun hm => hlarge G K had hN hm S hb)

/-- Apply the two uniform estimates to any family of admissible transforms;
both the group and the field may vary with the index. -/
theorem finiteCostBounds_of_uniform {ι : Type*} (G : ι → Type u) (K : ι → Type v)
    [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, Field (K i)]
    (had : ∀ i, Admissible (G i) (K i))
    (hlo : UniformFourierBorderLower.{u,v}) (hhi : UniformFourierUpper.{u,v}) :
    FiniteCostBounds (fun i => Fintype.card (G i))
      (fun i => complexity (fourierMatrix (G i) (K i))) := by
  obtain ⟨c, hc, h⟩ := hlo
  refine ⟨⟨c, hc, ?_⟩, ?_⟩
  · intro i hN
    exact h _ _ (had i) hN _ (realizableAtMost_complexity _).geometricBorder
  · intro ε hε
    obtain ⟨C, hC, h⟩ := hhi ε hε
    exact ⟨C, hC, fun i hN => h _ _ (had i) hN⟩

/-- An unconditional interval for the two complexities on every admissible
input. Each dense output needs a state, and dot products give the upper bound. -/
theorem fourier_linear_quadratic_bounds (G : Type u) (K : Type v)
    [AddCommGroup G] [Fintype G] [Field K] (h : Admissible G K) (hN : 2 ≤ Fintype.card G) :
    let N := Fintype.card G
    N ≤ complexity (fourierMatrix G K) ∧ complexity (fourierMatrix G K) ≤ N ^ 2 ∧
    N ≤ complexity (inverseFourierMatrix G K) ∧ complexity (inverseFourierMatrix G K) ≤ N ^ 2 := by
  dsimp only
  rw [complexity_inverseFourierMatrix G K h]
  have hlo := (fourier_border_card_le G K h hN _).1 (realizableAtMost_complexity _).geometricBorder
  have hhi := (complexity_le_iff _ _).mpr (realizableAtMost_card_mul_card (fourierMatrix G K))
  rw [card_character G K h, ← sq] at hhi
  exact ⟨hlo, hhi, hlo, hhi⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
