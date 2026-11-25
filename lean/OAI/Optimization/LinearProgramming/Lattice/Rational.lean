import OAI.Optimization.LinearProgramming.Lattice.Oracle

/-! Sign-preserving rounding applied directly to a rational reward or coefficient vector. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType

/-- Answer an integer sign query with a rational scalar product. -/
def rationalSignOracle {p : ℕ} (v : Fin p → ℚ) (a : Fin p → ℤ) : SignType :=
  sign (dotProduct (fun i => (a i : ℚ)) v)

theorem rationalSignOracle_correct {p : ℕ} (v : Fin p → ℚ) (a : Fin p → ℤ) :
    rationalSignOracle v a = sign (dotProduct (realCoordinates a) (fun i => (v i : ℝ))) := by
  have he : ((dotProduct (fun i => (a i : ℚ)) v : ℚ) : ℝ) =
      dotProduct (realCoordinates a) (fun i => (v i : ℝ)) := by
    simp [realCoordinates, dotProduct]
  rw [← he]
  simp [rationalSignOracle, sign_apply]

/-- Integer comparison vector computed from a rational input, with no access to input bits. -/
def roundRational {p : ℕ} (M : ℕ) (v : Fin p → ℚ) : Fin p → ℤ :=
  SignQueries.run (fun c => decide (0 ≤ rationalSignOracle v c)) (oracleRoundingProgram p M)

theorem roundRational_correct {p M : ℕ} (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℚ) :
    (∀ i, (roundRational M v i).natAbs.size ≤ radixWidth p M * p) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a (roundRational M v)) = sign (dotProduct (fun i => (a i : ℚ)) v) := by
  have h := oracleRoundingProgram_correct hp hM (fun i => (v i : ℝ)) (rationalSignOracle v)
    (rationalSignOracle_correct v)
  exact ⟨h.2.1, fun a ha => (h.2.2 a ha).trans (rationalSignOracle_correct v a).symm⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
