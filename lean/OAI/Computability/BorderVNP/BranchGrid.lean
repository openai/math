import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Tactic

/-! # Grids for the choices in Proposition 9.2

The coefficients of the excluded hypersurface can lie in a larger field than the grid.
In particular, the last hypersurface in the slicing construction has rational-function
coefficients while the grid consists of constants.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Finset MvPolynomial

/-- A nonzero polynomial has a nonzero value on a grid of side greater than its degree. -/
theorem exists_grid_eval_ne_zero {R : Type*} [CommRing R] [IsDomain R] {h : ℕ}
    {P : MvPolynomial (Fin h) R} (hP : P ≠ 0) (S : Finset R) (hS : P.totalDegree < S.card) :
    ∃ x : Fin h → R, (∀ i, x i ∈ S) ∧ eval x P ≠ 0 := by
  classical
  by_contra! hvan
  have hfilter : (Fintype.piFinset fun _ : Fin h ↦ S).filter (fun x ↦ eval x P = 0) =
      Fintype.piFinset fun _ : Fin h ↦ S := by
    apply filter_true_of_mem
    intro x hx
    exact hvan x (Fintype.mem_piFinset.mp hx)
  have hz := schwartz_zippel_totalDegree hP S
  rw [hfilter, Fintype.card_piFinset] at hz
  have hc : (0 : ℚ≥0) < S.card := by exact_mod_cast Nat.zero_lt_of_lt hS
  have hn : (S.card : ℚ≥0) ^ h ≠ 0 := pow_ne_zero _ hc.ne'
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
    div_self hn] at hz
  have := (le_div_iff₀ hc).mp hz
  norm_cast at this
  omega

/-- One constant tuple avoids all the specified hypersurfaces simultaneously, including
hypersurfaces with coefficients in an extension of the finite field of constants. -/
theorem exists_constants_avoiding {E R : Type*} [Field E] [Fintype E] [Field R]
    (ι : E →+* R) {h k : ℕ} (P : Fin k → MvPolynomial (Fin h) R) (hne : ∀ j, P j ≠ 0)
    (hsize : (∑ j, (P j).totalDegree) < Fintype.card E) :
    ∃ x : Fin h → E, ∀ j, eval (ι ∘ x) (P j) ≠ 0 := by
  classical
  let S := Finset.univ.map ⟨ι, ι.injective⟩
  let Q := ∏ j, P j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ hne j
  have hdeg : Q.totalDegree < S.card := by
    apply lt_of_le_of_lt (MvPolynomial.totalDegree_finsetProd ..)
    simpa [S] using hsize
  obtain ⟨y, hy, hyQ⟩ := exists_grid_eval_ne_zero hQ S hdeg
  have hy' : ∀ i, ∃ a : E, ι a = y i := by
    intro i
    simpa [S] using hy i
  choose x hx using hy'
  refine ⟨x, fun j ↦ ?_⟩
  have he : ι ∘ x = y := funext hx
  rw [he]
  rw [show Q = ∏ j, P j from rfl, map_prod, Finset.prod_ne_zero_iff] at hyQ
  exact hyQ j (mem_univ j)

end Branch

end BorderVNP
end Computability
end OAI
