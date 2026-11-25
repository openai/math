import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-! The envelope of nonnegative compressed circuit vectors and the separation
test at a designated coordinate (Section 2). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Finset Matrix
open scoped BigOperators

variable {ι : Type*}

/-- The coordinate maximum over the normalized circuit representatives,
including zero so the definition also applies to the empty family. -/
noncomputable def circuitEnvelope (C : Finset (ι → ℝ)) (i : ι) : ℝ := by
  classical
  exact (insert 0 (C.image (fun c => c i))).max' (insert_nonempty _ _)

theorem circuitEnvelope_nonneg (C : Finset (ι → ℝ)) (i : ι) :
    0 ≤ circuitEnvelope C i := by
  classical
  exact le_max' _ _ (mem_insert_self _ _)

theorem le_circuitEnvelope {C : Finset (ι → ℝ)} {c : ι → ℝ} (hc : c ∈ C) (i : ι) :
    c i ≤ circuitEnvelope C i := by
  classical
  exact le_max' _ _ (mem_insert_of_mem (mem_image_of_mem (fun d : ι → ℝ => d i) hc))

theorem circuitEnvelope_attained {C : Finset (ι → ℝ)} {i : ι} (h : 0 < circuitEnvelope C i) :
    ∃ c ∈ C, c i = circuitEnvelope C i := by
  classical
  have hm : circuitEnvelope C i ∈ insert 0 (C.image (fun c => c i)) :=
    max'_mem _ _
  exact mem_image.mp ((mem_insert.mp hm).resolve_left (ne_of_gt h))

/-- Finite logarithmic cost on the active coordinates of the envelope.
The algorithm uses this quantity only in the proof. -/
noncomputable def circuitCost (C : Finset (ι → ℝ)) (i : ι) : ℝ :=
  -Real.logb 2 (circuitEnvelope C i)

/-- Rescaling a normalized representative at the given signed prices, before
its final normalization. Supplying the negative prices gives the dual formula. -/
noncomputable def pricedVector (t c : ι → ℝ) (i : ι) : ℝ :=
  (2 : ℝ) ^ (-t i) * c i

private theorem priced_envelope_eq {C : Finset (ι → ℝ)} (t : ι → ℝ) {i : ι}
    (hi : 0 < circuitEnvelope C i) :
    pricedVector t (circuitEnvelope C) i = (2 : ℝ) ^ (-(circuitCost C i + t i)) := by
  rw [pricedVector, neg_add_rev, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp [circuitCost, Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hi]

/-- A coordinate within two of the least priced active cost reaches at least
one quarter of the largest scaled coordinate of one of the representatives.
The normalizer is explicitly attained, so the returned vector belongs to the
same normalized family as in (2.3) and (2.4). -/
theorem exists_priced_circuit_witness [Fintype ι]
    {C : Finset (ι → ℝ)} (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j)
    (t : ι → ℝ) (i : ι) (hi : 0 < circuitEnvelope C i)
    (hnear : ∀ j, 0 < circuitEnvelope C j →
      circuitCost C i + t i ≤ circuitCost C j + t j + 2) :
    ∃ c ∈ C, ∃ k, 0 < pricedVector t c k ∧
        (∀ j, 0 ≤ pricedVector t c j / pricedVector t c k ∧
          pricedVector t c j / pricedVector t c k ≤ 1) ∧
        1 / 4 ≤ pricedVector t c i / pricedVector t c k := by
  classical
  obtain ⟨c, hc, hci⟩ := circuitEnvelope_attained hi
  have hci' : pricedVector t c i = pricedVector t (circuitEnvelope C) i := by
    simp [pricedVector, hci]
  have hn j : 0 ≤ pricedVector t c j :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hC c hc j)
  have hp : 0 < pricedVector t c i :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (hci.symm ▸ hi)
  obtain ⟨k, _, hk⟩ := univ.exists_max_image (pricedVector t c) ⟨i, mem_univ _⟩
  have hkp : 0 < pricedVector t c k := hp.trans_le (hk i (mem_univ _))
  refine ⟨c, hc, k, hkp, fun j => ⟨div_nonneg (hn j) hkp.le,
    (div_le_one hkp).mpr (hk j (mem_univ _))⟩, (le_div_iff₀ hkp).mpr ?_⟩
  have hck : 0 < c k := pos_of_mul_pos_right hkp (Real.rpow_nonneg (by norm_num) _)
  have hen := hck.trans_le (le_circuitEnvelope hc k)
  have hcomp : pricedVector t c k ≤ 4 * pricedVector t c i := by
    calc
      pricedVector t c k ≤ pricedVector t (circuitEnvelope C) k :=
        mul_le_mul_of_nonneg_left (le_circuitEnvelope hc k) (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (-(circuitCost C k + t k)) := priced_envelope_eq t hen
      _ ≤ (2 : ℝ) ^ (2 + -(circuitCost C i + t i)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hnear k hen])
      _ = 4 * pricedVector t c i := by
        rw [hci', priced_envelope_eq t hi, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
  linarith

/-- The squared Euclidean length used by the rational projection test. -/
def squareLength [Fintype ι] (x : ι → ℝ) : ℝ := ∑ j, x j ^ 2

theorem abs_coordinate_le_of_squareLength_le [Fintype ι] {x : ι → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hx : squareLength x ≤ r ^ 2) (j : ι) : |x j| ≤ r := by
  classical
  have h : x j ^ 2 ≤ squareLength x :=
    single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg (x k)) (mem_univ j)
  nlinarith [sq_abs (x j), abs_nonneg (x j)]

/-- A vector in the designated test box cannot have small residual when a
dual witness has a large designated coordinate and a small projection. -/
theorem dual_witness_excludes_small_residual [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.IsSymm) (i : ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (hsmall : 2 * (Fintype.card ι : ℝ) * τ < 1 / 16)
    {y z : ι → ℝ} (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (hz : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hyi : 1 / 4 ≤ y i) (hzi : 1 / 4 ≤ z i)
    (hpy : squareLength (P *ᵥ y) ≤ τ ^ 2) :
    ¬ squareLength (z - P *ᵥ z) ≤ τ ^ 2 := by
  classical
  intro hpz
  have hl : 1 / 16 ≤ z ⬝ᵥ y := by
    calc
      1 / 16 = (1 / 4 : ℝ) * (1 / 4) := by norm_num
      _ ≤ z i * y i := mul_le_mul hzi hyi (by norm_num) (hz i).1
      _ ≤ z ⬝ᵥ y := single_le_sum (f := fun j => z j * y j)
        (fun j _ => mul_nonneg (hz j).1 (hy j).1) (mem_univ i)
  have bounded (a b : ι → ℝ) (ha : ∀ j, |a j| ≤ τ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
      a ⬝ᵥ b ≤ (Fintype.card ι : ℝ) * τ := by
    calc
      a ⬝ᵥ b ≤ ∑ _j : ι, τ := sum_le_sum (fun j _ => by
        calc
          a j * b j ≤ τ * b j := mul_le_mul_of_nonneg_right
            ((le_abs_self _).trans (ha j)) (hb j).1
          _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (hb j).2 hτ
          _ = τ := mul_one _)
      _ = _ := by simp
  have heq : z ⬝ᵥ (P *ᵥ y) = (P *ᵥ z) ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hP.eq]
  have h₁ := bounded (P *ᵥ y) z (abs_coordinate_le_of_squareLength_le hτ hpy) hz
  have h₂ := bounded (z - P *ᵥ z) y (abs_coordinate_le_of_squareLength_le hτ hpz) hy
  rw [dotProduct_comm (P *ᵥ y), heq] at h₁
  rw [sub_dotProduct] at h₂
  linarith

end Geometry
end LinearProgramming
end Optimization
end OAI
