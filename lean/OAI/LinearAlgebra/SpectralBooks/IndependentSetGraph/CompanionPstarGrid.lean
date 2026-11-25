import OAI.Computability.BorderVNP.TransferInteger
import OAI.Computability.VPVNP.PolynomialBounds
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.HamiltonianProjectionHardness

/-! # Subcubic independent-set projections onto the companion's signed polynomial -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace IndependentSetGraph
open Filter
open scoped Classical
universe u

/-- The integral Hamiltonian reduction and the signed independent-set gadgets
project to the same paired polynomial over every field, including characteristic two. -/
theorem companionPstar_gridProjections (F : Type u) [Field F] :
    ∃ A b : ℕ, 0 < A ∧ 0 < b ∧ ∀ᶠ n : ℕ in atTop,
      ∀ N : ℕ, A*n^b ≤ N → Nonempty (GridProjection F (Fin n × Bool)
        (MvPolynomial.map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n)) N) := by
  obtain ⟨j,_,poly,_,order,projected,_⟩ := OAI.Computability.BorderVNP.uniform_matrix_projections_with_order.{u}
  have bound := ((poly.pow 3).add poly).add
    ((OAI.Computability.VPVNP.PolynomiallyBounded.const 25).mul ((poly.pow 6).add (poly.pow 3)))
  obtain ⟨A,b,start,hbound⟩ := bound
  apply gridProjections_of_hamiltonian _ j (fun n => (order n).1) (A:=A) (b:=b)
  · exact eventually_atTop.mpr ⟨start,hbound⟩
  · intro n
    obtain ⟨p,hp⟩ := projected n F
    refine ⟨p,?_⟩
    rw [hamiltonianCyclePolynomial_eq_spanning F (m:=j n) (by have := (order n).1; omega)]
    exact hp

/-- A degree-component lower bound for the companion's explicit polynomial
at positive stretched exponent supplies the subcubic grids used by the Tree theorem. -/
theorem hardSubcubicGrids_of_companionPstar {F : Type*} [Field F] {ε : ℝ} (hε : 0 < ε)
    (hard : ∀ᶠ n : ℕ in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^ε))
      (MvPolynomial.map (Int.castRingHom F) (OAI.Computability.BorderVNP.Pstar n))) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ := by
  obtain ⟨A,b,hA,hb,projected⟩ := companionPstar_gridProjections F
  have hb' : 0 < (b:ℝ) := by exact_mod_cast hb
  have pos : 0 < ε / b := div_pos hε hb'
  refine ⟨(ε/b)/2,by positivity,?_⟩
  exact hardSubcubicGrids_of_polynomial_projections _ hA hb projected hε (by positivity) (by linarith) hard

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
