import OAI.Optimization.LinearProgramming.Lattice.LLLIndependence
import OAI.Optimization.LinearProgramming.Lattice.ProjectionMatrix
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size

/-! The Gram determinant as a common denominator for the rational residual projector. -/

open scoped BigOperators RealInnerProductSpace
open Submodule Matrix WithLp

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {p k : ℕ}

/-- Span of the rows of a real matrix, regarded as Euclidean vectors. -/
def euclideanRowSpan (A : Matrix (Fin k) (Fin p) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  span ℝ (Set.range fun i => toLp 2 (A i))

private theorem transpose_mulVec_mem_rowSpan (A : Matrix (Fin k) (Fin p) ℝ) (c : Fin k → ℝ) :
    toLp 2 (Aᵀ *ᵥ c) ∈ euclideanRowSpan A := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).2
  refine ⟨c, ?_⟩
  apply WithLp.ofLp_injective
  funext j
  simp [WithLp.ofLp_sum, Matrix.mulVec, dotProduct, mul_comm]

private theorem orthogonal_row_iff (A : Matrix (Fin k) (Fin p) ℝ) (x : Fin p → ℝ) :
    toLp 2 x ∈ (euclideanRowSpan A)ᗮ ↔ A *ᵥ x = 0 := by
  have hinner (i : Fin k) : inner ℝ (toLp 2 (A i)) (toLp 2 x) = (A *ᵥ x) i := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Matrix.mulVec, dotProduct, mul_comm]
  constructor
  · intro h
    funext i
    rw [← hinner]
    exact Submodule.inner_right_of_mem_orthogonal
      (show toLp 2 (A i) ∈ euclideanRowSpan A from Submodule.subset_span ⟨i, rfl⟩) h
  · intro h
    apply (Submodule.mem_orthogonal _ _).2
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      rw [hinner, h]; rfl
    | zero => simp
    | add a b _ _ ia ib => simp [inner_add_left, ia, ib]
    | smul r a _ ia => simp [inner_smul_left, ia]

/-- Multiplying the projection by the Gram determinant eliminates the inverse.
This identity also describes the integer numerator on integer inputs. -/
theorem gramDet_smul_residual (A : Matrix (Fin k) (Fin p) ℝ) (v : Fin p → ℝ)
    (hn : (A * Aᵀ).det ≠ 0) :
    (A * Aᵀ).det • (residual (euclideanRowSpan A) v).ofLp =
      (A * Aᵀ).det • v - Aᵀ *ᵥ (A * Aᵀ).adjugate *ᵥ A *ᵥ v := by
  let G := A * Aᵀ
  let c := G.det⁻¹ • (G.adjugate *ᵥ A *ᵥ v)
  let y := Aᵀ *ᵥ c
  have hAy : A *ᵥ y = A *ᵥ v := calc
    _ = G *ᵥ c := Matrix.mulVec_mulVec ..
    _ = G.det⁻¹ • ((G * G.adjugate) *ᵥ (A *ᵥ v)) := by
      rw [show c = _ from rfl, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    _ = A *ᵥ v := by
      rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        inv_mul_cancel₀ hn, one_smul]
  have hy : (euclideanRowSpan A).starProjection (toLp 2 v) = toLp 2 y := by
    apply Submodule.eq_starProjection_of_mem_orthogonal (transpose_mulVec_mem_rowSpan A c)
    apply (orthogonal_row_iff A (v - y)).2
    rw [Matrix.mulVec_sub, hAy, sub_self]
  unfold residual
  rw [hy]
  change G.det • (v - Aᵀ *ᵥ c) = G.det • v - Aᵀ *ᵥ G.adjugate *ᵥ A *ᵥ v
  rw [smul_sub, show c = _ from rfl, Matrix.mulVec_smul, smul_smul,
    mul_inv_cancel₀ hn, one_smul]

private theorem euclideanGram_eq (A : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.gram ℝ (fun i => toLp 2 (A i)) = A * Aᵀ := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Integer matrix with the directions as rows, in list order. -/
def integerRows (zs : List (Fin p → ℤ)) : Matrix (Fin zs.length) (Fin p) ℤ := fun i => zs.get i

private theorem span_list_le_iff (zs : List (Fin p → ℤ)) (T : Submodule ℝ (EuclideanSpace ℝ (Fin p))) :
    integerDirectionSpan zs ≤ T ↔ ∀ z ∈ zs, toLp 2 (realCoordinates z) ∈ T := by
  induction zs with
  | nil => simp [integerDirectionSpan]
  | cons z zs ih =>
    simp [integerDirectionSpan, sup_le_iff, span_singleton_le_iff_mem, ih, and_comm]

private theorem rowSpan_integerRows (zs : List (Fin p → ℤ)) :
    euclideanRowSpan ((integerRows zs).map (Int.castRingHom ℝ)) = integerDirectionSpan zs := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ((span_list_le_iff zs _).1 le_rfl) (zs.get i) (List.get_mem ..)
  · apply (span_list_le_iff zs _).2
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩


private theorem intMatrix_mulVec_cast {n : ℕ} (A : Matrix (Fin n) (Fin p) ℤ)
    (v : Fin p → ℤ) : realCoordinates (A *ᵥ v) = (A.map (Int.castRingHom ℝ)) *ᵥ realCoordinates v := by
  ext i
  exact (Int.castRingHom ℝ).map_mulVec A v i

private theorem intGram_cast (A : Matrix (Fin k) (Fin p) ℤ) :
    (A * Aᵀ).map (Int.castRingHom ℝ) =
      A.map (Int.castRingHom ℝ) * (A.map (Int.castRingHom ℝ))ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

private theorem intGram_det_cast (A : Matrix (Fin k) (Fin p) ℤ) :
    ((A * Aᵀ).det : ℝ) = (A.map (Int.castRingHom ℝ) * (A.map (Int.castRingHom ℝ))ᵀ).det := by
  exact ((Int.castRingHom ℝ).map_det (A * Aᵀ)).trans (congrArg det (intGram_cast A))

private theorem intGram_adj_cast (A : Matrix (Fin k) (Fin p) ℤ) :
    (A * Aᵀ).adjugate.map (Int.castRingHom ℝ) =
      (A.map (Int.castRingHom ℝ) * (A.map (Int.castRingHom ℝ))ᵀ).adjugate := by
  exact ((Int.castRingHom ℝ).map_adjugate (A * Aᵀ)).trans (congrArg Matrix.adjugate (intGram_cast A))

/-- The integer Gram determinant of the previously selected directions. -/
noncomputable def integerGramDet (zs : List (Fin p → ℤ)) : ℤ :=
  (integerRows zs * (integerRows zs)ᵀ).det

theorem integerGramDet_ne_zero (zs : List (Fin p → ℤ))
    (hli : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i)))) :
    integerGramDet zs ≠ 0 := by
  have hh : Matrix.gram ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))) =
      (integerRows zs).map (Int.castRingHom ℝ) * ((integerRows zs).map (Int.castRingHom ℝ))ᵀ :=
    euclideanGram_eq _
  have hx := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hli
  rw [hh, ← intGram_det_cast] at hx
  exact_mod_cast hx

private theorem residual_at_coordinate (zs : List (Fin p → ℤ)) (j i : Fin p) :
    (residual (integerDirectionSpan zs) (Pi.single j 1)) i = (rationalResidualMatrix zs i j : ℝ) := by
  rw [← rationalResidualMatrix_correct, realMatrixApply, Matrix.mulVec_single_one]
  rfl

theorem rationalResidualMatrix_entry_abs_le_one (zs : List (Fin p → ℤ)) (i j : Fin p) :
    |rationalResidualMatrix zs i j| ≤ 1 := by
  have hx : |(rationalResidualMatrix zs i j : ℝ)| ≤ 1 := by
    rw [← residual_at_coordinate, ← Real.norm_eq_abs]
    have h := PiLp.norm_apply_le (residual (integerDirectionSpan zs) (Pi.single j 1)) i
    apply h.trans
    rw [residual, ← Submodule.starProjection_orthogonal_val]
    exact (Submodule.norm_starProjection_apply_le _ _).trans_eq (by simp)
  exact_mod_cast hx

/-- Every entry of the residual projector has the same available integer denominator.
This uses the Gram determinant of the original integer directions, independently of
the denominators in preceding projector updates. -/
theorem integerGramDet_mul_entry (zs : List (Fin p → ℤ)) (hn : integerGramDet zs ≠ 0)
    (i j : Fin p) : ∃ n : ℤ, (integerGramDet zs : ℚ) * rationalResidualMatrix zs i j = n := by
  let A := integerRows zs
  let f := Int.castRingHom ℝ
  let G := A * Aᵀ
  let e : Fin p → ℤ := Pi.single j 1
  let N := G.det • e - Aᵀ *ᵥ G.adjugate *ᵥ A *ᵥ e
  have hdet : ((A.map f) * (A.map f)ᵀ).det ≠ 0 := by
    rw [← intGram_det_cast]
    exact_mod_cast hn
  have hx := gramDet_smul_residual (A.map f) (realCoordinates e) hdet
  rw [← intGram_det_cast, rowSpan_integerRows] at hx
  have hN : realCoordinates N =
      (G.det : ℝ) • realCoordinates e - (A.map f)ᵀ *ᵥ
        (A.map f * (A.map f)ᵀ).adjugate *ᵥ (A.map f) *ᵥ realCoordinates e := by
    have hv : realCoordinates (Aᵀ *ᵥ G.adjugate *ᵥ A *ᵥ e) = (A.map f)ᵀ *ᵥ
        (A.map f * (A.map f)ᵀ).adjugate *ᵥ (A.map f) *ᵥ realCoordinates e := by
      rw [intMatrix_mulVec_cast, intMatrix_mulVec_cast, intMatrix_mulVec_cast, intGram_adj_cast A]
      rfl
    ext l
    change ((G.det * e l - (Aᵀ *ᵥ G.adjugate *ᵥ A *ᵥ e) l : ℤ) : ℝ) = _
    rw [Int.cast_sub, Int.cast_mul]
    exact congrArg (fun t => (G.det : ℝ) * e l - t) (congrFun hv l)
  rw [← hN] at hx
  have he : realCoordinates e = Pi.single j 1 := by
    ext l
    by_cases hl : l = j <;> simp [e, realCoordinates, hl]
  have hi := congrFun hx i
  change (integerGramDet zs : ℝ) * (residual (integerDirectionSpan zs) (realCoordinates e)) i = (N i : ℝ) at hi
  rw [he, residual_at_coordinate] at hi
  refine ⟨N i, ?_⟩
  exact_mod_cast hi

/-- The reduced denominator divides the Gram determinant, not just a product
of all intermediate denominators. -/
theorem rationalResidualMatrix_den_dvd (zs : List (Fin p → ℤ)) (hn : integerGramDet zs ≠ 0)
    (i j : Fin p) : ((rationalResidualMatrix zs i j).den : ℤ) ∣ integerGramDet zs := by
  obtain ⟨n, hh⟩ := integerGramDet_mul_entry zs hn i j
  have heq : rationalResidualMatrix zs i j = (n : ℚ) / integerGramDet zs := by
    apply (eq_div_iff (by exact_mod_cast hn : (integerGramDet zs : ℚ) ≠ 0)).mpr
    rw [mul_comm, hh]
  rw [heq, Rat.intCast_div_eq_divInt]
  exact Rat.den_dvd ..


private theorem gram_height_pow_bound {k p D : ℕ} (hkp : k ≤ p) :
    k.factorial * (p * D ^ 2) ^ k ≤ 2 ^ ((2 * p + 2 * D.size) * p) := by
  have hD : D ≤ 2 ^ D.size := (Nat.size_le.mp (show D.size ≤ D.size by rfl)).le
  have hp : p ≤ 2 ^ p := Nat.lt_two_pow_self.le
  calc
    _ ≤ k ^ k * (p * D ^ 2) ^ k := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
    _ = (k * (p * D ^ 2)) ^ k := (Nat.mul_pow ..).symm
    _ ≤ (2 ^ p * (2 ^ p * (2 ^ D.size) ^ 2)) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (hkp.trans hp)
        (Nat.mul_le_mul hp (Nat.pow_le_pow_left hD _))) _
    _ = 2 ^ ((2 * p + 2 * D.size) * k) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hkp)

/-- Uniform numerator and denominator bit lengths for the projector used by the oracle.
Lengths depend on the original integer directions, even when the projector is updated
recursively. The dimension also bounds the number of independent directions. -/
theorem rationalResidualMatrix_entry_size (zs : List (Fin p → ℤ)) {D : ℕ}
    (hkp : zs.length ≤ p) (hcoord : ∀ z ∈ zs, ∀ i, (z i).natAbs ≤ D)
    (hli : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))))
    (i j : Fin p) :
    (rationalResidualMatrix zs i j).num.natAbs.size ≤ (2*p + 2*D.size)*p + 1 ∧
    (rationalResidualMatrix zs i j).den.size ≤ (2*p + 2*D.size)*p + 1 := by
  let r := rationalResidualMatrix zs i j
  have hn := integerGramDet_ne_zero zs hli
  have hdvd : (r.den : ℤ) ∣ integerGramDet zs := rationalResidualMatrix_den_dvd zs hn i j
  have hdvd' : r.den ∣ (integerGramDet zs).natAbs := by
    exact_mod_cast Int.dvd_natAbs.mpr hdvd
  have hden : r.den ≤ (integerGramDet zs).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hdvd'
  have hrabs : |r| ≤ 1 := rationalResidualMatrix_entry_abs_le_one zs i j
  have hpden : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  rw [← Rat.num_div_den r, abs_div, abs_of_pos hpden, div_le_one hpden] at hrabs
  have hnumZ : |r.num| ≤ (r.den : ℤ) := by exact_mod_cast hrabs
  rw [Int.abs_eq_natAbs] at hnumZ
  have hnum : r.num.natAbs ≤ r.den := by exact_mod_cast hnumZ
  have hGram : (integerGramDet zs).natAbs ≤ 2 ^ ((2*p + 2*D.size)*p) :=
    (gram_det_bound (integerRows zs) (fun a l => hcoord _ (List.get_mem ..) l)).trans
      (gram_height_pow_bound hkp)
  have hbound := hden.trans hGram
  have hbits := Nat.size_le_size hbound
  rw [Nat.size_pow] at hbits
  exact ⟨(Nat.size_le_size hnum).trans hbits, hbits⟩


/-- A direction outside the previous span extends the independent list, as required
to carry the Gram determinant bound along the executed rounding loop. -/
theorem integerDirectionList_independent_cons (zs : List (Fin p → ℤ)) (z : Fin p → ℤ)
    (hold : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))))
    (hnew : toLp 2 (realCoordinates z) ∉ integerDirectionSpan zs) :
    LinearIndependent ℝ (fun i : Fin (z :: zs).length => toLp 2 (realCoordinates ((z :: zs).get i))) := by
  have hspan : Submodule.span ℝ (Set.range fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))) =
      integerDirectionSpan zs := rowSpan_integerRows zs
  rw [← hspan] at hnew
  have hcons : (fun i : Fin (z :: zs).length => toLp 2 (realCoordinates ((z :: zs).get i))) =
      Fin.cons (toLp 2 (realCoordinates z)) (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hcons]
  exact hold.finCons hnew

end Lattice
end LinearProgramming
end Optimization
end OAI
