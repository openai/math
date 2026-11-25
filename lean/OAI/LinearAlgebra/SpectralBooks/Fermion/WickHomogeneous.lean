import OAI.LinearAlgebra.SpectralBooks.Fermion.WickPolynomial

/-! # The degree of a monochromatic normal product -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open LaurentPolynomial

private theorem weight_erase_cast {α : State} {r : ℕ} (hr : r ∈ α) :
    (weight (α.erase r) : ℤ) + (2 * r + 1) = weight α := by
  exact_mod_cast (Finset.sum_erase_add α (fun i : ℕ ↦ 2*i+1) hr)

private theorem modeDegree_create (l : List ℕ) (j : ℕ) (α β : State) {r : ℕ} (hr : r ∈ α) :
    modeDegree l (α.erase r) β = modeDegree (j :: l) α β - r + j := by
  unfold modeDegree
  rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
  push_cast
  have hw := weight_erase_cast hr
  omega

private theorem modeDegree_annihilate (l : List ℕ) (j : ℕ) (α β : State) {r : ℕ} (hr : r ∈ β) :
    modeDegree l α (β.erase r) = modeDegree (j :: l) α β + r + 1 + j := by
  unfold modeDegree
  rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
  push_cast
  have hw := weight_erase_cast hr
  omega

private theorem combine_modes (x s y d e : ℤ) :
    (C x * T d : LaurentPolynomial ℤ) * C s * (C y * T e) = C (x*s*y) * T (d+e) := by
  rw [T_add, map_mul, map_mul]
  ring

/-- A word evaluated in one variable has a single possible monomial. Its coefficient is
the integral field mode, even when the degree parity forces that coefficient to vanish. -/
theorem mixedNormal_one_variable (side : Bool) (l : List ℕ) (α β : State) :
    mixedNormal (l.map (Prod.mk side)) α β =
      C (listMode l (modeDegree l α β) α β) * T (fieldExponent side (modeDegree l α β)) := by
  induction l generalizing α β with
  | nil =>
    by_cases he : α = β
    · subst β
      simp [modeDegree, listWeight, fieldExponent, mixedNormal, listMode]
    · simp [mixedNormal, listMode, he]
  | cons j l ih =>
    rw [List.map_cons, mixedNormal, listMode, map_add, add_mul]
    simp only [List.length_map, map_mul, map_pow, map_neg, map_one, map_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [ih, creationCoeff, combine_modes, modeDegree_create l j α β hr]
      rw [← map_mul, ← map_mul]
      congr 2
      cases side <;> simp [fieldExponent]
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [ih, annihilationCoeff, combine_modes, modeDegree_annihilate l j α β hr]
      rw [← map_mul, ← map_mul]
      congr 2
      cases side <;> simp [fieldExponent]

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
