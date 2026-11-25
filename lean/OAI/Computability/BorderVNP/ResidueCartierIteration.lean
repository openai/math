import OAI.Computability.BorderVNP.ResidueAmbientJet
import OAI.Computability.BorderVNP.ResiduePins

/-!
# Iteration of the branch change-of-coordinates formula

Lemma 10.2 can be verified first for the characteristic power. At each successive
iteration, the pullout identity on the ambient chart adds the missing equation
powers. This gives exactly the exponent `p^u − 1` in every equation of the chart.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open ResidueBox
open scoped LaurentSeries BigOperators

variable {σ ι E K : Type*} [Field E] [Field K]

/-- Two successive extractions on a branch have the product Frobenius power. -/
theorem branchCartier_comp (p u v : ℕ) [ExpChar K p] [PerfectRing K p] (D : LaurentSeries K) :
    cartier p u (cartier p v D) = cartier p (u + v) D := by
  ext i
  simp only [cartier_coeff, iterateFrobeniusEquiv_symm_add_apply]
  congr 3
  simp only [pow_add, Nat.cast_mul]
  ring

/-- At the zeroth Frobenius iterate the Laurent polynomial coefficient operator is the identity. -/
theorem ambientCartier_iter_zero (p : ℕ) [ExpChar E p] [PerfectRing E p] (f : Laurent σ E) :
    ambientCartier p 0 f = f := by
  ext e
  rw [ambientCartier_coeff]
  apply (iterateFrobeniusEquiv E p 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, pow_zero, pow_one]
  congr 1
  funext i
  simp [sourceIndex]

/-- At the zeroth Frobenius iterate the Laurent series coefficient operator is the identity. -/
theorem branchCartier_iter_zero (p : ℕ) [ExpChar K p] [PerfectRing K p] (D : LaurentSeries K) :
    cartier p 0 D = D := by
  ext i
  rw [cartier_coeff]
  apply (iterateFrobeniusEquiv K p 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, pow_zero, pow_one]
  simp

private theorem equationProduct_eq_pow [Fintype ι] (q : ℕ)
    (g : ι → MvPolynomial (Option σ) E) :
    equationProduct q g = (toLaurent (∏ i, g i)) ^ (q - 1) := by
  rw [equationProduct, Finset.prod_pow, map_pow]

/-- The two weights before two ambient extractions give precisely the equation product
for their combined exponent. -/
theorem ambientCartier_equations_comp [Fintype ι] (p u v : ℕ)
    [ExpChar E p] [PerfectRing E p] (g : ι → MvPolynomial (Option σ) E) (f : Laurent σ E) :
    ambientCartier p u (ambientCartier p v (f * equationProduct (p ^ v) g) *
      equationProduct (p ^ u) g) =
    ambientCartier p (u + v) (f * equationProduct (p ^ (u + v)) g) := by
  simp only [equationProduct_eq_pow]
  let G := toLaurent (∏ i, g i)
  let a := p ^ u - 1
  let b := p ^ v - 1
  change ambientCartier p u (ambientCartier p v (f * G^b) * G^a) =
    ambientCartier p (u + v) (f * G ^ (p ^ (u + v) - 1))
  have hexp : a * p ^ v + b = p ^ (u + v) - 1 := by
    have hu := expChar_pow_pos E p u
    have hv := expChar_pow_pos E p v
    have ha : a + 1 = p ^ u := Nat.sub_add_cancel hu
    have hb : b + 1 = p ^ v := Nat.sub_add_cancel hv
    rw [pow_add, ← ha, add_mul, one_mul]
    omega
  rw [mul_comm _ (G ^ a), ← ambientCartier_pow_mul, ambientCartier_comp, ← pow_mul, ← hexp,
    pow_add]
  ring_nf

/-- The characteristic-power case of (10.2) implies all positive iterates, for the same
branch differential, chart equations and coefficient embedding. -/
theorem branch_formula_iterate [Fintype σ] [Fintype ι] (p : ℕ)
    [ExpChar E p] [PerfectRing E p] [ExpChar K p] [PerfectRing K p]
    (g : ι → MvPolynomial (Option σ) E) (φ : E →+* LaurentSeries K)
    (x : σ → LaurentSeries K) (t : (LaurentSeries K)ˣ) (η₀ : LaurentSeries K)
    (step : ∀ f : Mixed σ E, ∃ z : Mixed σ E,
      mixedToLaurent z =
        ambientCartier p 1 (mixedToLaurent f * equationProduct (p ^ 1) g) ∧
      cartier p 1 (mixedEval φ x t f * η₀) = mixedEval φ x t z * η₀)
    (u : ℕ) (f : Mixed σ E) : ∃ z : Mixed σ E,
      mixedToLaurent z = ambientCartier p u (mixedToLaurent f * equationProduct (p ^ u) g) ∧
      cartier p u (mixedEval φ x t f * η₀) = mixedEval φ x t z * η₀ := by
  induction u with
  | zero => exact ⟨f, by simp [equationProduct_eq_pow, ambientCartier_iter_zero],
      by rw [branchCartier_iter_zero]⟩
  | succ u ih =>
    obtain ⟨z, hpoly, hbranch⟩ := ih
    obtain ⟨w, hpol', hbranch'⟩ := step z
    refine ⟨w, ?_, ?_⟩
    · rw [hpol', hpoly, ambientCartier_equations_comp, Nat.add_comm 1 u]
    · rw [Nat.add_comm u 1, ← branchCartier_comp, hbranch, hbranch']

/-- The iterated formula supplies the change-of-coordinates input to the actual matrix pins. -/
theorem pin_compatibility_iterate [Fintype σ] [Fintype ι] (p : ℕ) [Fact p.Prime]
    [CharP E p] [PerfectRing E p] [CharP K p] [PerfectRing K p]
    (g : ι → MvPolynomial (Option σ) E) (φ : E →+* LaurentSeries K)
    (x : σ → LaurentSeries K) (t : (LaurentSeries K)ˣ) (η₀ : LaurentSeries K)
    (step : ∀ f : Mixed σ E, ∃ z : Mixed σ E,
      mixedToLaurent z =
        ambientCartier p 1 (mixedToLaurent f * equationProduct (p ^ 1) g) ∧
      cartier p 1 (mixedEval φ x t f * η₀) = mixedEval φ x t z * η₀)
    (u : ℕ) : ResiduePins.CartierCompatibility p φ x t η₀ u g
      (iterateFrobeniusEquiv E p u).symm.toRingHom := by
  intro f
  obtain ⟨z, hpoly, hbranch⟩ := branch_formula_iterate p g φ x t η₀ step u f
  change ResiduePins.evaluate φ x t (ambientCartier p u
    (mixedToLaurent f * equationProduct (p ^ u) g)) * η₀ = _
  rw [← hpoly, ResiduePins.evaluate_embed, hbranch]

end Residue

end BorderVNP
end Computability
end OAI
