import OAI.LinearAlgebra.SpectralBooks.GridRecurrence
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchFormula

/-! # The edgeless case in the independent-set grid lower bound

For an edgeless graph all occupancy bits are independent. Its polynomial
therefore has a linear-size exact formula. A family satisfying the Tree border
lower bound eventually has an edge, so both classes of its grid are nonempty.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped BigOperators Classical
namespace IndependentSetGrid

open PlanarPatch MvPolynomial Filter

variable {m n : ℕ}

/-- For an edgeless bipartite graph the polynomial is a product of linear forms,
one factor for every vertex, including isolated vertices. -/
theorem polynomial_edgeless {R : Type*} [CommSemiring R] {E : Fin m → Fin n → Prop}
    (h : ∀ i j, ¬E i j) :
    polynomial (R := R) E = ∏ v : Fin m ⊕ Fin n, (X (v,false) + X (v,true)) := by
  have hi (b : Bits m n) : Independent E b := fun i j he => (h i j he).elim
  rw [polynomial, generatingSum, Fintype.prod_sum_type]
  simp only [hi, ite_true, Fintype.sum_prod_type]
  calc
    _ = (∑ b : Fin m → Bool, ∏ i, X (R := R) (Sum.inl i,b i)) *
        ∑ b : Fin n → Bool, ∏ j, X (R := R) (Sum.inr j,b j) :=
      (Fintype.sum_mul_sum _ _).symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (i : Fin m) (b : Bool) => X (R := R) (Sum.inl (β := Fin n) i,b)),
        ← Fintype.prod_sum (fun (j : Fin n) (b : Bool) => X (R := R) (Sum.inr (α := Fin m) j,b))]
      simp [add_comm]

variable {F : Type*} [Field F]

private theorem pairProduct_formula {I : Type*} (r : ℕ) (v : Fin r → I) :
    HasFormula (2*r+1)
      (∏ i, (X (R := F) (v i,false) + X (v i,true))) := by
  induction r with
  | zero => simpa using HasFormula.const (I := I × Bool) (1 : F)
  | succ r ih =>
    rw [Fin.prod_univ_succ]
    exact (((HasFormula.input (F := F) (v 0,false)).add
      (HasFormula.input (v 0,true))).mul (ih (fun i => v i.succ))).mono (by omega)

/-- One addition and at most one multiplication per graph vertex suffice. -/
theorem programCost_edgeless {E : Fin m → Fin n → Prop} (h : ∀ i j, ¬E i j) :
    polynomialProgramCost (polynomial (R := F) E) ≤ 2*(m+n) := by
  rw [polynomial_edgeless h]
  let L := Fin m ⊕ Fin n
  let e := (Fintype.equivFin L).symm
  have hprod := pairProduct_formula (F := F) (Fintype.card L) e
  rw [Equiv.prod_comp e (fun v => X (R := F) (v,false) + X (v,true))] at hprod
  obtain ⟨P,hP,hC⟩ := hprod
  have bound := polynomialProgramCost_le P.compile.program P.compile.output
  rw [registerPolynomial_compile, hP, P.compile.cost_eq] at bound
  have hc : Fintype.card L = m+n := by simp [L]
  rw [hc] at hC
  exact bound.trans (by omega)

/-- A stretched-exponential degree-component border lower bound forces an edge
for all sufficiently large graph orders. -/
theorem eventually_exists_edge [Infinite F] (m k : ℕ → ℕ)
    (E : (n : ℕ) → Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n in atTop, m n + k n = n)
    {δ : ℝ} (hδ : 0 < δ)
    (lower : ∀ᶠ n in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^δ))
      (polynomial (R := F) (E n))) :
    ∀ᶠ n in atTop, ∃ i j, E n i j := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have gap := eventually_grid_exponent_lt (N := id) (p := 0) (δ := δ) (by norm_num) (by simpa using hδ)
    (inv_pos.mpr hlog) (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      change 0 < n ∧ (n:ℝ) ≤ (n:ℝ)^2/4 + 2*n
      exact ⟨hn, by nlinarith [sq_nonneg (n:ℝ), Nat.cast_nonneg (α := ℝ) n]⟩)
  filter_upwards [gap, order, lower, eventually_gt_atTop (0 : ℕ)] with n hgap hn hl hpos
  by_contra! hedges
  obtain ⟨r,P,o,hP,hC⟩ := exists_program_of_cost (polynomial (R := F) (E n))
  have hc := programCost_edgeless (F := F) hedges
  rw [hn, ← hC] at hc
  have hborder := (degreeBorderSize_le_program n P o).trans hc
  rw [hP] at hborder
  have hlower : (2:ℝ)^((n:ℝ)^δ) ≤ 2*n := by
    change _ ≤ (degreeBorderSize n _ : ℝ) at hl
    exact hl.trans (by exact_mod_cast hborder)
  have hlogb : Real.logb 2 (2*(n:ℝ)) < (n:ℝ)^δ := by
    simpa [Real.logb, div_eq_inv_mul, id] using hgap
  exact ((Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mp hlogb).not_ge hlower

/-- Both dimensions of the rectangular grid are eventually positive. -/
theorem eventually_positive_classes [Infinite F] (m k : ℕ → ℕ)
    (E : (n : ℕ) → Fin (m n) → Fin (k n) → Prop)
    (order : ∀ᶠ n in atTop, m n + k n = n)
    {δ : ℝ} (hδ : 0 < δ)
    (lower : ∀ᶠ n in atTop, DegreeBorderSizeAtLeast n ((2:ℝ)^((n:ℝ)^δ))
      (polynomial (R := F) (E n))) :
    ∀ᶠ n in atTop, 0 < m n ∧ 0 < k n := by
  filter_upwards [eventually_exists_edge m k E order hδ lower] with n ⟨i,j,_⟩
  exact ⟨Nat.zero_lt_of_lt i.isLt, Nat.zero_lt_of_lt j.isLt⟩

end IndependentSetGrid

end

end SpectralBooks
end LinearAlgebra
end OAI
