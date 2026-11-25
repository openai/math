import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Basic.Real.Basic
import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.Farkas.Basic
import OAI.Optimization.LinearProgramming.Farkas.Sparse
import Mathlib.Tactic

/-! Projected inequalities and the integer certificates obtained from independent columns. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {K : Type*}

open Finset Matrix
open scoped BigOperators Matrix

section FarkasProjection

variable {K ι ν : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype ι] [Fintype ν]

/-- Every nonnegative multiplier annihilating the hidden columns is valid on their projection. -/
theorem projected_inequality_of_witness (H : Matrix ι ν K) (r : ι → K) (y : ν → K)
    (hy : H *ᵥ y ≤ r) (w : ι → K) (hw : 0 ≤ w) (hH : Hᵀ *ᵥ w = 0) :
    0 ≤ w ⬝ᵥ r := by
  have h := dotProduct_le_dotProduct_of_nonneg_left hy hw
  rwa [dotProduct_mulVec, ← mulVec_transpose, hH, zero_dotProduct] at h

omit [Fintype ν] in
/-- A violating multiplier can always be normalized to have mass one. -/
theorem normalize_violating_multiplier (H : Matrix ι ν K) (r : ι → K)
    (w : ι → K) (hw : 0 ≤ w) (hH : Hᵀ *ᵥ w = 0) (hr : w ⬝ᵥ r < 0) :
    ∃ v : ι → K, 0 ≤ v ∧ Hᵀ *ᵥ v = 0 ∧ (∑ i, v i) = 1 ∧ v ⬝ᵥ r < 0 := by
  have hw0 : ∃ i, 0 < w i := by
    by_contra! h
    have hwz : w = 0 := funext fun i => le_antisymm (h i) (hw i)
    simp [hwz] at hr
  obtain ⟨i, hi⟩ := hw0
  have hsum : 0 < ∑ i, w i := sum_pos' (fun j _ => hw j) ⟨i, mem_univ i, hi⟩
  refine ⟨(∑ i, w i)⁻¹ • w, fun j => mul_nonneg (inv_nonneg.mpr hsum.le) (hw j), ?_, ?_, ?_⟩
  · rw [mulVec_smul, hH, smul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, inv_mul_cancel₀ hsum.ne']
  · rw [smul_dotProduct, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hsum) hr

end FarkasProjection

section IntegerGram

variable {ι ν : Type*} [Fintype ι] [Fintype ν] [DecidableEq ν]

/-- For independent columns the domain Gram system is nonsingular, even if the original
system is rectangular. This lets its determinant bounds use only the column count. -/
theorem det_gram_ne_zero_of_independent {M : Matrix ι ν ℝ}
    (hM : LinearIndependent ℝ M.col) : (Mᵀ * M).det ≠ 0 := by
  apply nonsingular_iff_det_ne_zero.mp
  apply Nonsingular.of_linearIndependent_col
  apply mulVec_injective_iff.mp
  change Function.Injective (Mᵀ * M).mulVecLin
  rw [← LinearMap.ker_eq_bot, ker_mulVecLin_transpose_mul_self, LinearMap.ker_eq_bot]
  exact mulVec_injective_iff.mpr hM

omit [DecidableEq ν] in
/-- Integral normal equations for the unique solution of a rectangular linear system. -/
theorem integer_gram_equations (A : Matrix ι ν ℤ) (b : ι → ℤ) (z : ν → ℝ)
    (hz : (A.map (Int.cast : ℤ → ℝ)) *ᵥ z = (fun j => (b j : ℝ))) :
    ((Aᵀ * A).map (Int.cast : ℤ → ℝ)) *ᵥ z = (fun j => ((Aᵀ *ᵥ b) j : ℝ)) := by
  have h := congrArg ((A.map (Int.cast : ℤ → ℝ))ᵀ *ᵥ ·) hz
  have hg : (Aᵀ * A).map (Int.cast : ℤ → ℝ) =
      (A.map (Int.cast : ℤ → ℝ))ᵀ * (A.map (Int.cast : ℤ → ℝ)) := by
    ext i j; simp [Matrix.mul_apply]
  have hb : (fun j => ((Aᵀ *ᵥ b) j : ℝ)) =
      (A.map (Int.cast : ℤ → ℝ))ᵀ *ᵥ (fun j => (b j : ℝ)) := by
    ext j; simp [Matrix.mulVec, dotProduct]
  rwa [hg, hb, ← mulVec_mulVec]

/-- Determinant bounds for an injective rectangular system, without a minor selection.
All coordinates have one positive denominator and uniformly bounded numerators. -/
theorem exists_bounded_scaled_integer_solution (A : Matrix ι ν ℤ) (b : ι → ℤ)
    (z : ν → ℝ) (hcol : LinearIndependent ℝ (A.map (Int.cast : ℤ → ℝ)).col)
    (hz : (A.map (Int.cast : ℤ → ℝ)) *ᵥ z = (fun j => (b j : ℝ)))
    {B : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ B) (hb : ∀ i, (b i).natAbs ≤ B) :
    let T := (Fintype.card ν).factorial * (Fintype.card ι * B ^ 2) ^ Fintype.card ν
    ∃ (q : ℤ) (w : ν → ℤ), 0 < q ∧ q.natAbs ≤ T^2 ∧
      (∀ i, (w i).natAbs ≤ T^2) ∧ ∀ i, (w i : ℝ) = (q : ℝ) * z i := by
  classical
  let G : Matrix ν ν ℤ := Aᵀ * A
  let c : ν → ℤ := Aᵀ *ᵥ b
  have hG : G.map (Int.cast : ℤ → ℝ) =
      (A.map (Int.cast : ℤ → ℝ))ᵀ * A.map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [G, Matrix.mul_apply]
  have hdet : G.det ≠ 0 := by
    intro hf
    apply det_gram_ne_zero_of_independent hcol
    rw [← hG, ← Int.cast_det, hf, Int.cast_zero]
  have hbd (f g : ι → ℤ) (hf : ∀ j, (f j).natAbs ≤ B) (hg : ∀ j, (g j).natAbs ≤ B) :
      (∑ j, f j * g j).natAbs ≤ Fintype.card ι * B ^ 2 := by
    suffices h : |∑ j, f j * g j| ≤ ((Fintype.card ι : ℕ) : ℤ) * (B : ℤ) ^ 2 by
      exact_mod_cast (show ((∑ j, f j * g j).natAbs : ℤ) ≤ _ from (Int.natCast_natAbs _).symm ▸ h)
    calc
      _ ≤ ∑ j, |f j * g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, (B : ℤ)^2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, pow_two, ← Int.natCast_natAbs, ← Int.natCast_natAbs]
        exact_mod_cast Nat.mul_le_mul (hf j) (hg j)
      _ = _ := by simp
  have hgB (i j : ν) : (G i j).natAbs ≤ Fintype.card ι * B ^ 2 :=
    hbd (fun k => A k i) (fun k => A k j) (fun k => hA k i) (fun k => hA k j)
  have hcB (j : ν) : (c j).natAbs ≤ Fintype.card ι * B ^ 2 :=
    hbd (fun k => A k j) b (fun k => hA k j) hb
  have hD := det_natAbs_le_factorial_mul_pow G hgB
  have hN (i : ν) := det_natAbs_le_factorial_mul_pow (G.updateCol i c)
      (B := Fintype.card ι * B^2) (fun j k => by
        by_cases h : k = i
        · subst k; simpa using hcB j
        · simpa [Matrix.updateCol_ne h] using hgB j k)
  refine ⟨G.det * G.det, fun i => G.det * (G.updateCol i c).det,
    mul_self_pos.mpr hdet, ?_, ?_, ?_⟩
  · simpa [Int.natAbs_mul, pow_two] using Nat.mul_le_mul hD hD
  · intro i
    simpa [Int.natAbs_mul, pow_two] using Nat.mul_le_mul hD (hN i)
  · intro i
    have h := cramer_coordinate G c z hdet (integer_gram_equations A b z hz) i
    have he := (eq_div_iff (Int.cast_ne_zero.mpr hdet)).mp h
    simp only [Int.cast_mul]
    rw [← he]
    ring

end IntegerGram

section BoundedProjection

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- A uniform bound for each nonnegative integer multiplier needed to eliminate d hidden
variables from a system with integral coefficients of magnitude at most B. -/
def projectionMultiplierBound (d B : ℕ) : ℕ :=
  ((d+1).factorial * ((d+1) * max 1 B ^ 2)^(d+1))^2

/-- Every violated projected cut has a certificate supported on at most d+1 original rows.
Its integer weights are bounded independently of the number of original constraints or the
possibly irrational residuals r. -/
theorem bounded_integer_obstruction (H : Matrix ι (Fin d) ℤ) (r : ι → ℝ) {B : ℕ}
    (hH : ∀ i j, (H i j).natAbs ≤ B)
    (hempty : ¬ ∃ y, H.map (Int.cast : ℤ → ℝ) *ᵥ y ≤ r) :
    ∃ (t : Finset ι) (p : t → ℤ), t.card ≤ d + 1 ∧
      (∀ i, 0 ≤ p i ∧ (p i).natAbs ≤ projectionMultiplierBound d B) ∧
      (∀ j, ∑ i : t, p i * H i j = 0) ∧ ∑ i : t, (p i : ℝ) * r i < 0 := by
  classical
  let H' := H.map (Int.cast : ℤ → ℝ)
  obtain ⟨w, hw, hwH, hwr⟩ := (OAI.Optimization.LinearProgramming.Farkas.alternative d ι H' r).resolve_left hempty
  obtain ⟨v, hv, hvH, hvm, hvr⟩ := normalize_violating_multiplier H' r w hw hwH
    (by rwa [dotProduct_comm])
  obtain ⟨t, z, hind, hz, hzs, hzm, hzr⟩ := OAI.Optimization.LinearProgramming.Farkas.convex_sparse_min
    (fun i => H' i) r v hv
  have hcard : t.card ≤ d + 1 := by
    simpa [Module.finrank_prod] using hind.linearIndependent.fintype_card_le_finrank
  let A : Matrix (Option (Fin d)) t ℤ := of fun j i => j.elim 1 (fun k => H i k)
  let b : Option (Fin d) → ℤ := fun j => j.elim 1 (fun _ => 0)
  let e : ((Fin d → ℝ) × ℝ) ≃ₗ[ℝ] (Option (Fin d) → ℝ) :=
    (LinearEquiv.prodComm ℝ (Fin d → ℝ) ℝ).trans (LinearEquiv.piOptionEquivProd ℝ (M := fun _ : Option (Fin d) => ℝ)).symm
  have hAcol : LinearIndependent ℝ (A.map (Int.cast : ℤ → ℝ)).col := by
    convert hind.linearIndependent.map' e.toLinearMap e.ker using 1
    ext i j
    cases j with
    | none => change ((1 : ℤ) : ℝ) = 1; exact Int.cast_one
    | some _ => rfl
  have hsum (j : Fin d) : (∑ i ∈ t, z i * H' i j) = 0 := by
    have h := congrFun hzs j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.trans (by simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hvH j)
  have hx : (A.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i : t => z i) = (fun j => (b j : ℝ)) := by
    funext j
    cases j with
    | none =>
      simpa [A, b, Matrix.mulVec, dotProduct, ← t.sum_coe_sort] using hzm.trans hvm
    | some j =>
      simpa [A, b, H', Matrix.mulVec, dotProduct, ← t.sum_coe_sort, mul_comm] using hsum j
  obtain ⟨q, p, hq, _, hp, hpz⟩ := exists_bounded_scaled_integer_solution A b
    (fun i : t => z i) hAcol hx (B := max 1 B)
    (fun j i => by cases j with
      | none => simp [A]
      | some j => simpa [A] using (hH i j).trans (le_max_right 1 B))
    (fun j => by cases j <;> simp [b])
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨t, p, hcard, ?_, ?_, ?_⟩
  · intro i
    constructor
    · exact_mod_cast (show (0 : ℝ) ≤ (p i : ℝ) from (hpz i).symm ▸ mul_nonneg hqR.le (hz i i.property))
    · apply (hp i).trans
      simp only [Fintype.card_coe, Fintype.card_option, Fintype.card_fin, projectionMultiplierBound]
      gcongr
  · intro j
    suffices h : (∑ i : t, (p i : ℝ) * (H i j : ℝ)) = 0 by exact_mod_cast h
    simp only [hpz, mul_assoc, ← Finset.mul_sum]
    have h : (∑ i : t, z i * (H i j : ℝ)) = 0 := by
      simpa [H', ← t.sum_coe_sort] using hsum j
    rw [h, mul_zero]
  · simp only [hpz, mul_assoc, ← Finset.mul_sum]
    apply mul_neg_of_pos_of_neg hqR
    have h : ∑ i ∈ t, z i * r i < 0 := hzr.trans_lt hvr
    simpa only [← t.sum_coe_sort] using h

end BoundedProjection

end Compression
end LinearProgramming
end Optimization
end OAI
