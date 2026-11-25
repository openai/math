import OAI.Optimization.LinearProgramming.Lattice.Dirichlet
import Mathlib.Algebra.Order.Round

/-! A bounded, executable reference implementation of simultaneous rational approximation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

private def admissibleDenominators {p : ℕ} (Q : ℕ) (u : Fin p → ℚ) : Finset ℕ :=
  (Finset.Icc 1 (Q ^ p)).filter fun q ↦
    ∀ i, |(q : ℚ) * u i - round ((q : ℚ) * u i)| ≤ 1 / (Q : ℚ)

/-- Search for the least admissible common denominator and round each numerator.
The search is a reference algorithm with up to `Q ^ p` candidates. -/
def rationalDirichlet {p : ℕ} (Q : ℕ) (u : Fin p → ℚ) : ℕ × (Fin p → ℤ) :=
  let candidates := admissibleDenominators Q u
  let q := if h : candidates.Nonempty then candidates.min' h else 0
  (q, fun i ↦ round ((q : ℚ) * u i))

/-- The finite search succeeds on every positive grid parameter. -/
theorem rationalDirichlet_correct {p Q : ℕ} (hQ : 0 < Q) (u : Fin p → ℚ) :
    0 < (rationalDirichlet Q u).1 ∧ (rationalDirichlet Q u).1 ≤ Q ^ p ∧
      ∀ i, |((rationalDirichlet Q u).1 : ℚ) * u i - (rationalDirichlet Q u).2 i| ≤ 1 / (Q : ℚ) := by
  obtain ⟨q, hq, hb, z, hz⟩ := simultaneous_dirichlet hQ (fun i ↦ (u i : ℝ))
  have hm : q ∈ admissibleDenominators Q u := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq, hb⟩, fun i ↦ (round_le _ (z i)).trans ?_⟩
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using hz i
  have hne : (admissibleDenominators Q u).Nonempty := ⟨q, hm⟩
  have hmin := Finset.mem_filter.mp ((admissibleDenominators Q u).min'_mem hne)
  obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp hmin.1
  simp only [rationalDirichlet, dite_eq_left hne]
  exact ⟨lo, hi, hmin.2⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
