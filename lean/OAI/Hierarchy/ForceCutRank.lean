import OAI.Hierarchy.ABPFirstCutRank
import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import Mathlib.Tactic

namespace OAI
/-! # The force across a cut is bounded by the logarithm of its matrix rank -/

noncomputable section

namespace Hierarchy

open LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators InnerProductSpace

variable {F : Type*} [Field F] {I : Type} [Fintype I] [DecidableEq I]

namespace HomogeneousFlat

/-- Index the two sides of a finite cut. -/
def cutSide (U : Finset I) (i : I) : Fin 2 := if i ∈ U then 0 else 1

private theorem column_factors {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n F) :
    ∃ (L : m → Fin A.rank → F) (R : n → Fin A.rank → F),
      ∀ a b, A a b = ∑ k, L a k * R b k := by
  let W := Submodule.span F (Set.range A.col)
  let b := Module.finBasisOfFinrankEq F W A.rank_eq_finrank_span_cols.symm
  let col (j : n) : W := ⟨A.col j, Submodule.subset_span ⟨j,rfl⟩⟩
  refine ⟨fun a k => (b k).val a, fun j k => b.repr (col j) k, fun a j => ?_⟩
  have h := congrArg (fun v : W => v.val a) (b.sum_repr (col j))
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm, Matrix.col_apply, col] using h.symm

private theorem diagonal_coeffs (J : Type) [Fintype J] (n : ℕ) :
    (Raw.diagonal J F (Fin n)).coeff =
      Crossing.basisTensor (F := F) (A := fun _ : J => Fin n) (fun r _ => r) := by
  funext a
  simp only [Raw.diagonal, Crossing.basisTensor];
    apply Finset.sum_congr rfl; intro r _; split_ifs <;> rfl

set_option maxHeartbeats 1500000 in
/-- The grouped two-leg tensor is a local restriction of the diagonal whose size is the
matrix rank of the cut. This includes the empty and full cuts. -/
theorem grouped_restricts_rank_diagonal (T : Raw.{0} I F) (U : Finset I) :
    (T.group (cutSide U)).Restricts
      (Raw.diagonal (Fin 2) F (Fin (ABPFirstCut.flatten U T.coeff).rank)) := by
  classical
  let A := ABPFirstCut.flatten U T.coeff
  obtain ⟨rowFactor,columnFactor,factors⟩ := column_factors A
  let left (v : (T.group (cutSide U)).Leg 0) : ABPFirstCut.Inside T.Leg U :=
    fun i => v ⟨i.1, by simp [cutSide, i.2]⟩
  let right (v : (T.group (cutSide U)).Leg 1) : ABPFirstCut.Outside T.Leg U :=
    fun i => v ⟨i.1, by simp [cutSide, i.2]⟩
  let L (v : (T.group (cutSide U)).Leg 0) (k : Fin A.rank) : F := rowFactor (left v) k
  let R (v : (T.group (cutSide U)).Leg 1) (k : Fin A.rank) : F := columnFactor (right v) k
  let M : (j : Fin 2) → (T.group (cutSide U)).Leg j → Fin A.rank → F :=
    Fin.cons L (Fin.cons R (fun i => Fin.elim0 i))
  change Crossing.IsRestriction (T.group (cutSide U)).coeff (Raw.diagonal (Fin 2) F (Fin A.rank)).coeff
  rw [diagonal_coeffs (F := F) (Fin 2) A.rank]
  apply (Crossing.restriction_basisTensor_iff (fun (k : Fin A.rank) (_ : Fin 2) => k)
    (T.group (cutSide U)).coeff).mpr
  refine ⟨M,fun v => ?_⟩
  have regroup : (T.group (cutSide U)).coeff v = A (left (v 0)) (right (v 1)) := by
    apply congrArg T.coeff
    funext i
    have transport (j : Fin 2) (h : cutSide U i = j) :
        v (cutSide U i) ⟨i,rfl⟩ = v j ⟨i,h⟩ := by cases h; rfl
    by_cases h : i ∈ U
    · simpa only [ABPFirstCut.join, dite_eq_left h, left] using transport 0 (by simp [cutSide,h])
    · simpa only [ABPFirstCut.join, dite_eq_right h, right] using transport 1 (by simp [cutSide,h])
  rw [regroup]
  simp only [Fin.prod_univ_two]
  exact factors (left (v 0)) (right (v 1))

/-- The two-site placement in directions `z` and `0` costs at most distance times log rank. -/
theorem cut_price_le {d : ℕ} (P : HomogeneousFlat F d) (T : Raw.{0} I F)
    (hne : T.coeff ≠ 0) (U : Finset I) (z : EuclideanSpace ℝ (Fin d)) :
    P.prices.price T (fun i => if i ∈ U then z else 0) ≤
      ‖z‖ * Real.logb 2 (ABPFirstCut.flatten U T.coeff).rank := by
  classical
  by_cases hz : z = 0
  · subst z
    simp [P.prices.collapsed]
  let Y : Fin 2 ↪ EuclideanSpace ℝ (Fin d) :=
    ⟨![z,0], by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨φ,_,hn⟩ := P.prices.normalized_group Y
  have placement : (fun i => if i ∈ U then z else 0) = Y ∘ cutSide U := by
    funext i
    by_cases h : i ∈ U <;> simp [Y, cutSide, h] <;> rfl
  rw [placement,hn (cutSide U) T hne,P.prices.wire]
  change dist z 0 * _ ≤ _
  rw [dist_zero_right]
  have h := rawLogPrice_mono φ (norm_nonneg z) (grouped_restricts_rank_diagonal T U)
  simpa only [rawLogPrice, ofRaw_diagonal_fin_eq_natCast,
    show ∀ n : ℕ, φ.val (n : TensorClass (Fin 2) F) = n from
      fun n => map_natCast (normalizedSpectrum.toRingHom φ) n, NNReal.coe_natCast] using h

/-- A single jointly supporting force configuration obeys this inequality for every cut. -/
theorem force_cut_rank {d : ℕ} (P : HomogeneousFlat F d) (T : Raw.{0} I F)
    (hne : T.coeff ≠ 0) (g : I → EuclideanSpace ℝ (Fin d))
    (h : ∀ y, (∑ i, ⟪g i, y i⟫_ℝ) ≤ P.prices.price T y) (U : Finset I) :
    ‖∑ i ∈ U, g i‖ ≤ Real.logb 2 (ABPFirstCut.flatten U T.coeff).rank := by
  classical
  let z := ∑ i ∈ U, g i
  have hc := (h (fun i => if i ∈ U then z else 0)).trans (P.cut_price_le T hne U z)
  have hi : (∑ i, ⟪g i, if i ∈ U then z else 0⟫_ℝ) = ‖z‖ * ‖z‖ := by
    have terms (i : I) : ⟪g i, if i ∈ U then z else 0⟫_ℝ =
        if i ∈ U then ⟪g i,z⟫_ℝ else 0 := by by_cases h : i ∈ U <;> simp [h]
    simp_rw [terms]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← sum_inner]
    exact real_inner_self_eq_norm_mul_norm z
  rw [hi] at hc
  by_cases hn : 0 < ‖z‖
  · exact (mul_le_mul_iff_right₀ hn).mp hc
  · have hz := le_antisymm (le_of_not_gt hn) (norm_nonneg z)
    change ‖z‖ ≤ _
    rw [hz]
    cases hr : (ABPFirstCut.flatten U T.coeff).rank with
    | zero => simp
    | succ n => exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

end HomogeneousFlat
end Hierarchy

end
end OAI
