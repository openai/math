import OAI.LinearAlgebra.SpectralBooks.ZariskiCurve
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! # Powers of tensors in an affine Zariski closure

A linear functional of the coefficients of an `n`th tensor power is a
polynomial in the original coefficients. The powers of points of a Zariski
closure therefore lie in the span of the powers of the original points.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {K ι : Type*} [Field K]

/-- The coordinates of the `n`th tensor power, collecting sites in any format. -/
def coordinatePower (n : ℕ) (x : ι → K) (w : Fin n → ι) : K := ∏ j, x (w j)

/-- Every linear subspace of a finite-dimensional coordinate space is affine
Zariski closed. -/
theorem affineZariskiClosure_submodule {κ : Type*} [Fintype κ] (U : Submodule K (κ → K)) :
    affineZariskiClosure (U : Set (κ → K)) = U := by
  classical
  apply Set.Subset.antisymm _ (subset_affineZariskiClosure _)
  intro x hx
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U x).mp
  intro f hf
  let e (i : κ) : κ → K := fun j ↦ if i = j then 1 else 0
  let p : MvPolynomial κ K := ∑ i, MvPolynomial.C (f (e i)) * MvPolynomial.X i
  have hp (y : κ → K) : MvPolynomial.eval y p = f y := by
    have hy : ∑ i, y i • e i = y := by
      ext j
      simp [e, Finset.sum_apply, Pi.smul_apply, mul_ite]
    simpa [p, mul_comm] using congrArg f hy
  rw [← hp x]
  apply hx p
  intro y hy
  rw [hp]
  exact (Submodule.mem_dualAnnihilator f).mp hf y hy

/-- Membership in the affine Zariski closure preserves linear-span constraints
on the coordinates of each tensor power. -/
theorem coordinatePower_mem_span_of_closure [Fintype ι] {S : Set (ι → K)}
    {x : ι → K} (hx : x ∈ affineZariskiClosure S) (n : ℕ) :
    coordinatePower n x ∈ Submodule.span K (coordinatePower n '' S) := by
  classical
  let f (w : Fin n → ι) : MvPolynomial ι K := ∏ j, MvPolynomial.X (w j)
  let U := Submodule.span K (coordinatePower n '' S)
  have heval (y : ι → K) (w : Fin n → ι) : MvPolynomial.eval y (f w) = coordinatePower n y w := by
    simp [f, coordinatePower]
  have hm : Set.MapsTo (fun y w ↦ MvPolynomial.eval y (f w)) S (U : Set _) := by
    intro y hy
    simp only [heval]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have hh := mapsTo_affineZariskiClosure_of_polynomial f hm hx
  simp only [affineZariskiClosure_submodule, heval] at hh
  exact hh

end SpectralBooks
end LinearAlgebra
end OAI
