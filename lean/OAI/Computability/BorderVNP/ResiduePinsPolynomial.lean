import OAI.Computability.BorderVNP.ResiduePins

/-! # Residue pins for an ordinary input polynomial

This is the coefficient indexing of (10.1): a monomial of the input polynomial has
zero exponent of the Laurent parameter. Its matrix is weighted by the coefficient
of that monomial. The degree bound on the complete polynomial supplies all coordinate
bounds needed by the finite test space.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open Residue ResidueBox Module Matrix
open scoped Matrix BigOperators Classical

variable {σ ι β E κ : Type*} [Field E] [Field κ] [Fintype σ] [Fintype ι] [Fintype β]

/-- The exponents of an ordinary polynomial in the mixed chart. -/
def polynomialIndex : (σ →₀ ℕ) →+ ((σ → ℕ) × ℤ) where
  toFun d := (d, 0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-- Embed a polynomial in the chart with no dependence on the invertible parameter. -/
noncomputable def polynomialChart : MvPolynomial σ E →+* Mixed σ E :=
  AddMonoidAlgebra.mapDomainRingHom E polynomialIndex

/-- Evaluating an ordinary polynomial in the chart agrees with formal polynomial evaluation. -/
theorem polynomialChart_eval {A : Type*} [CommRing A] (φ : E →+* A) (x : σ → A)
    (t : Aˣ) : (mixedEval φ x t).comp polynomialChart = MvPolynomial.eval₂Hom φ x := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    change mixedEval φ x t (AddMonoidAlgebra.mapDomain polynomialIndex (.single 0 c)) = φ c
    rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
    simp
  · intro i
    rw [MvPolynomial.eval₂Hom_X']
    change mixedEval φ x t (AddMonoidAlgebra.mapDomain polynomialIndex
      (.single (Finsupp.single i 1) 1)) = x i
    rw [AddMonoidAlgebra.mapDomain_single, mixedEval_single]
    simp only [polynomialIndex, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_mul,
      zpow_zero, Units.val_one]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
    · simp

/-- The eigenvector identity for every degree-bounded ordinary polynomial regular at the
branch with value in the prime field. The matrix indices on the left are its own monomials. -/
theorem polynomial_eigenvector (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E]
    [Algebra (ZMod p) κ] [CharP κ p] [PerfectRing κ p]
    (φ : E →+* LaurentSeries κ) (x : σ → LaurentSeries κ) (t : (LaurentSeries κ)ˣ)
    (η₀ : LaurentSeries κ) (B : Basis β (ZMod p) E) (L u : ℕ) (hq : 2 ≤ p ^ u)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E)
    (hCartier : CartierCompatibility p φ x t η₀ u g root)
    (A : MvPolynomial σ E) (hL : A.totalDegree ≤ L) (z : ZMod p)
    (hregular : 0 ≤ (MvPolynomial.eval₂ φ x A).order)
    (hvalue : (MvPolynomial.eval₂ φ x A).coeff 0 = algebraMap (ZMod p) κ z)
    (hpole : ∀ i : Index β σ (radius L (∑ j, (g j).totalDegree)),
      -((p ^ u : ℕ) : ℤ) ≤ (evaluate φ x t (test B i) * η₀).order) :
    let H := radius L (∑ j, (g j).totalDegree)
    let Ω := pin B H (testFunctional p φ x t η₀)
    (∑ μ ∈ A.support,
      weights B H (p ^ u) (by omega) g root (mixedIndex (polynomialIndex μ)) (A.coeff μ)) *ᵥ Ω =
        z • Ω := by
  let H := radius L (∑ j, (g j).totalDegree)
  let F := mixedToLaurent (polynomialChart A)
  let I := mixedIndex.comp (polynomialIndex (σ := σ))
  have hcoeff : F.coeff = A.coeff.mapDomain I := by
    change (A.coeff.mapDomain polynomialIndex).mapDomain mixedIndex = _
    exact Finsupp.mapDomain_comp.symm
  have hb (d : Exponent σ) (hd : d ∈ F.coeff.support) :
      d none = 0 ∧ ∀ i, 0 ≤ d (some i) ∧ d (some i) ≤ L := by
    rw [hcoeff] at hd
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hd)
    refine ⟨rfl, fun i => ⟨Int.natCast_nonneg _, ?_⟩⟩
    change (μ i : ℤ) ≤ (L : ℤ)
    exact_mod_cast (MvPolynomial.le_degreeOf_of_mem_support i hμ).trans
      ((A.degreeOf_le_totalDegree i).trans hL)
  have heval : evaluate φ x t F = MvPolynomial.eval₂ φ x A := by
    rw [show F = mixedToLaurent (polynomialChart A) from rfl, evaluate_embed]
    exact RingHom.congr_fun (polynomialChart_eval φ x t) A
  have he := eigenvector p φ x t η₀ B L u hq g root hCartier F z hb
    (heval ▸ hregular) (heval ▸ hvalue) hpole
  let W := weights B H (p ^ u) (by omega) g root
  have hs : F.coeff.sum (fun d c => W d c) = A.coeff.sum (fun μ a => W (I μ) a) := by
    rw [hcoeff]
    exact Finsupp.sum_mapDomain_index_addMonoidHom (fun d => (W d).toAddMonoidHom)
  change F.coeff.sum (fun d c => W d c) *ᵥ _ = _ at he
  rw [hs] at he
  exact he

end ResiduePins

end BorderVNP
end Computability
end OAI
