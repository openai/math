import OAI.Computability.BorderVNP.CoverLorentzMatrix
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Minkowski reduction for the quaternion tiles

The integral quaternion basis has covolume 24 in row-major matrix coordinates.
Right multiplication by a special linear matrix preserves that covolume.
Minkowski's convex body theorem therefore puts a nonzero integral quaternion
translate inside a single bounded box independently of the translating matrix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix MeasureTheory MeasureTheory.Measure Set

/-- For every determinant-one matrix a nonzero integral quaternion translates into the cube
of radius three. This is the bounded-set assertion on page 15 of the manuscript. -/
theorem exists_bounded_translate (g : Mat) (hg : g.det = 1) :
    ∃ x : Order, x ≠ 0 ∧ ∀ i j, |(split x*g) i j| ≤ 3 := by
  classical
  let b := Pi.basisFun ℝ (Fin 4)
  let A := (rightMatrix g).toLin'
  let box := Icc (fun _ : Fin 4 => (-3 : ℝ)) (fun _ => 3)
  have hdet : A.det = 24 := by simp [A, LinearMap.det_toLin', det_rightMatrix,hg]
  have hD : volume (ZSpan.fundamentalDomain b) ≤ 1 := by
    calc
      _ ≤ volume (Icc (fun _ : Fin 4 => (0 : ℝ)) (fun _ => 1)) := by
        apply measure_mono
        intro v hv
        have h (i : Fin 4) : 0 ≤ v i ∧ v i < 1 := hv i
        exact ⟨fun i => (h i).1,fun i => (h i).2.le⟩
      _ = 1 := by simp [Real.volume_Icc_pi]
  have hbox : volume box = 1296 := by norm_num [box,Real.volume_Icc_pi,Fin.prod_univ_four]
  have hvol : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin 4 → ℝ) <
      volume (A ⁻¹' box) := by
    rw [Measure.addHaar_preimage_linearMap volume (hdet ▸ by norm_num),hdet,hbox]
    apply lt_of_le_of_lt (mul_le_mul_left hD _)
    rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
    norm_num [Module.finrank_pi, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  have hs : ∀ x ∈ A ⁻¹' box, -x ∈ A ⁻¹' box := by
    intro x hx
    change (fun _ : Fin 4 => (-3:ℝ)) ≤ A x ∧ A x ≤ (fun _ => 3) at hx
    change (fun _ : Fin 4 => (-3:ℝ)) ≤ A (-x) ∧ A (-x) ≤ (fun _ => 3)
    rw [map_neg]
    exact ⟨fun i => neg_le_neg (hx.2 i), fun i => by simpa using neg_le_neg (hx.1 i)⟩
  have hc : Convex ℝ (A ⁻¹' box) := (convex_Icc _ _).linear_preimage A
  have : Countable (Submodule.span ℤ (range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (range b))
    infer_instance
  obtain ⟨v,hv,hin⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' b volume) hs hc hvol
  have hz (i : Fin 4) : ∃ z : ℤ, (z : ℝ) = v.val i :=
    ((Pi.basisFun ℝ (Fin 4)).mem_span_iff_repr_mem ℤ _).mp v.property i
  choose f hf using hz
  let x : Order := ⟨f 0,f 1,f 2,f 3⟩
  have he : ![(x.re:ℝ),x.imI,x.imJ,x.imK] = v.val := by
    funext i; fin_cases i <;> exact hf _
  refine ⟨x,?_,?_⟩
  · intro hx
    apply hv
    apply Subtype.ext
    rw [← he,hx]
    funext i; fin_cases i <;> simp
  · have hcoord := rightMatrix_coordinates g x
    rw [he] at hcoord
    change A v.val ∈ box at hin
    change (rightMatrix g).mulVec v.val ∈ box at hin
    rw [hcoord] at hin
    intro i j
    fin_cases i <;> fin_cases j
    · exact abs_le.mpr ⟨hin.1 0,hin.2 0⟩
    · exact abs_le.mpr ⟨hin.1 1,hin.2 1⟩
    · exact abs_le.mpr ⟨hin.1 2,hin.2 2⟩
    · exact abs_le.mpr ⟨hin.1 3,hin.2 3⟩

end Cover

end BorderVNP
end Computability
end OAI
