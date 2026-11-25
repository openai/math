import OAI.Computability.BorderVNP.OrderedRankDescent

/-!
# Border size using circuits with constants in the ground field

Section 2.1 takes the circuit image over the algebraic closure of the ground
field. This file compares that image with the Zariski closure of outputs of
circuits whose constants lie in the ground field. A lower bound for the
geometric image gives the same gate-count lower bound for this second model.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

variable {F σ : Type*} [Field F]

/-- Least size using the Zariski closure of the degree components of actual
circuits whose constants are drawn from `F`. -/
noncomputable def groundBorderSize (d : ℕ) (p : MvPolynomial σ F) : ℕ := by
  classical
  exact Nat.find (show ∃ s, geometricApprox d s p from ⟨_, geometricApprox_circuitSize d p⟩)

/-- Any approximation by ground-field circuits is allowed in the geometric model. -/
theorem borderApprox_of_ground {d s : ℕ} {p : MvPolynomial σ F}
    (hp : geometricApprox d s p) : BorderApprox d s p := by
  unfold BorderApprox geometricApprox
  rw [coeffVector_map]
  apply map_mem_imageClosure _ hp
  rintro _ ⟨m, hm, c, rfl⟩
  exact ⟨m, hm, c.mapConstants _, by rw [c.map_polynomial, coeffVector_map]⟩

/-- Transfers a geometric border-size lower bound to the literal ground-field
image at each length and in every characteristic. -/
theorem borderSize_le_groundBorderSize (d : ℕ) (p : MvPolynomial σ F) :
    borderSize d p ≤ groundBorderSize d p := by
  classical
  exact borderSize_le_iff.mpr (borderApprox_of_ground
    (Nat.find_spec (show ∃ s, geometricApprox d s p from ⟨_, geometricApprox_circuitSize d p⟩)))

/-- Over an infinite field the two minima agree. -/
theorem borderSize_eq_groundBorderSize [Infinite F] (d : ℕ) (p : MvPolynomial σ F) :
    borderSize d p = groundBorderSize d p := by
  classical
  refine le_antisymm (borderSize_le_groundBorderSize ..) (Nat.find_min' _ ?_)
  exact geometricApprox_of_baseChange (E := AlgebraicClosure F) (borderSize_spec d p)

namespace Ordered

private theorem exists_ground_approximation (d : ℕ) (p : WordPoly F σ) :
    ∃ s, coefficients d p ∈ imageClosure (degreeImage F σ d s) := by
  obtain ⟨m, c, hc⟩ := exists_output p
  exact ⟨m, subset_imageClosure _ ⟨m, le_rfl, c, congrArg (coefficients d) hc⟩⟩

/-- Least size for the closure of actual ground-field word coefficient vectors. -/
noncomputable def groundBorderSize (d : ℕ) (p : WordPoly F σ) : ℕ := by
  classical
  exact Nat.find (exists_ground_approximation d p)

/-- Extending the constants preserves an approximation of a word coefficient
vector on the ground-field image. -/
theorem approximates_of_ground {d s : ℕ} {p : WordPoly F σ}
    (hp : coefficients d p ∈ imageClosure (degreeImage F σ d s)) : approximates d s p := by
  apply map_mem_imageClosure _ hp
  rintro _ ⟨m, hm, c, rfl⟩
  exact ⟨m, hm, c.mapConstants _, coefficients_mapConstants ..⟩

/-- A geometric lower bound for ordered circuits applies to the original field. -/
theorem borderSize_le_groundBorderSize (d : ℕ) (p : WordPoly F σ) :
    borderSize d p ≤ groundBorderSize d p := by
  classical
  exact borderSize_le_iff.mpr (approximates_of_ground (Nat.find_spec (exists_ground_approximation d p)))

/-- The two ordered sizes agree for all infinite ground fields. -/
theorem borderSize_eq_groundBorderSize [Infinite F] (d : ℕ) (p : WordPoly F σ) :
    borderSize d p = groundBorderSize d p := by
  classical
  refine le_antisymm (borderSize_le_groundBorderSize ..) (Nat.find_min' _ ?_)
  exact (degreeImage_closure_extend_iff (E := AlgebraicClosure F) _).mp (borderSize_le_iff.mp le_rfl)

end Ordered

end BorderVNP
end Computability
end OAI
