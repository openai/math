import OAI.Computability.BorderVNP.DiagonalPaidColumns
import OAI.Computability.VPVNP.ClassSeparation

namespace OAI.Computability.VPVNP.Standalone

universe u

/-- Every exact arithmetic circuit for the signed path-count polynomial has at least
`2 ^ (c * (log₂ n) ^ (5/4))` gates. The constant is absolute, and the threshold
is uniform over all fields of a given characteristic. -/
theorem pstar_circuit_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      ∀ s : ℕ, Valiant.Project.Computes s (MvPolynomial.map (Int.castRingHom F) (BorderVNP.Pstar n)) →
        (2 : ℝ) ^ (c * (Real.logb 2 n) ^ (5 / 4 : ℝ)) ≤ (s : ℝ) := by
  obtain ⟨c, hc, bound⟩ := BorderVNP.Rate.uniform_rate_of_border_stretch.{u}
    BorderVNP.ProvedStretch.rational BorderVNP.ProvedStretch.prime
  refine ⟨c, hc, fun q => ?_⟩
  obtain ⟨N, hN⟩ := bound q
  refine ⟨N, fun n hn F _ _ s computes => ?_⟩
  obtain ⟨circuit, hpoly⟩ := Valiant.Project.computes_iff.mp computes
  have size := circuitSize_le_of_circuit circuit
  rw [hpoly] at size
  exact (hN n hn F).trans (Nat.cast_le.mpr ((BorderVNP.borderSize_le_circuitSize n _).trans
    size))

end OAI.Computability.VPVNP.Standalone
