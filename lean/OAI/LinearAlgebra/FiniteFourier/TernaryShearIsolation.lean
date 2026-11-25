import OAI.LinearAlgebra.FiniteFourier.TernaryCycleFourier
import OAI.LinearAlgebra.FiniteFourier.TernaryCycleUnits
import OAI.LinearAlgebra.FiniteFourier.SemilocalPivot

/-! # A unit shear on three coordinates

Changing one entry of a weighted cycle, then multiplying by the inverse of
the original cycle, changes only the first row. Two diagonal conjugates
cancel the spectator coefficient and leave a unit coefficient on port one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] {ζ : R}

private abbrev unitDiag (d : Fin 3 → Rˣ) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal fun i => (d i : R)

private theorem conjugateWord {A B : Matrix (Fin 3) (Fin 3) R} {n : ℕ}
    (hA : RingTernaryWord ζ n A) (d : Fin 3 → Rˣ)
    (h : unitDiag d * A = B * unitDiag d) : RingTernaryWord ζ (1 + n + 1) B := by
  have hd : unitDiag d * unitDiag (fun i => (d i)⁻¹) = 1 := by
    simp [unitDiag]
  have hw := ((RingTernaryWord.diagonal (ζ := ζ) d).mul hA).mul
    (RingTernaryWord.diagonal (fun i => (d i)⁻¹))
  change RingTernaryWord ζ _ ((unitDiag d * A) * unitDiag _) at hw
  rwa [h, Matrix.mul_assoc, hd, Matrix.mul_one] at hw

/-- The changed edge closes the cycle with weight `a⁴ = (a²)³/a²`. -/
private def changedCycle (a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, a^4; a, 1, 0; 0, a, 1]

private theorem changedCycleWord {a : R} (ha : IsUnit a)
    (h : RingTernaryWord ζ 4 (ternaryCycleSum (a^2))) :
    RingTernaryWord ζ 6 (changedCycle a) := by
  obtain ⟨u, rfl⟩ := ha
  apply conjugateWord h ![u^2, u, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitDiag, changedCycle, ternaryCycleSum] <;> ring

private def rowUpdate (x y : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, x, y; 0, 1, 0; 0, 0, 1]

private theorem normalizeRow {a t : R} (ht : (1 + a^3) * t = 1) (v : Rˣ)
    (hv : (v : R) * ((1 + a^6) * t) = 1)
    (hS : RingTernaryWord ζ 6 (changedCycle a))
    (hI : RingTernaryWord ζ 4 (ternaryCycleInv a t)) :
    RingTernaryWord ζ 11 (rowUpdate ((v : R) * (a^2-a^5) * t) ((v : R) * (a^4-a) * t)) := by
  let d : Fin 3 → Rˣ := ![v, 1, 1]
  have he : unitDiag d * (changedCycle a * ternaryCycleInv a t) =
      rowUpdate ((v : R) * (a^2-a^5) * t) ((v : R) * (a^4-a) * t) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [unitDiag, diagonal_mul] <;>
      norm_num [d, changedCycle, ternaryCycleInv, rowUpdate, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | linear_combination hv | linear_combination ht | ring
  rw [← he]
  exact (RingTernaryWord.diagonal d).mul (hS.mul hI)

private theorem isolateRow {x y : R} (hxy : RingTernaryWord ζ 11 (rowUpdate x y))
    (z : Rˣ) : RingTernaryWord ζ 26 (rowUpdate (((z : R) - 1) * x) 0) := by
  have h₁ : RingTernaryWord ζ 13 (rowUpdate ((z : R) * x) y) := by
    apply conjugateWord hxy ![z, 1, z]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [unitDiag, rowUpdate]
    ring
  have h₂ : RingTernaryWord ζ 13 (rowUpdate (-x) (-y)) := by
    apply conjugateWord hxy ![-1, 1, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [unitDiag, rowUpdate]
  have he : rowUpdate ((z : R) * x) y * rowUpdate (-x) (-y) = rowUpdate (((z : R)-1)*x) 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rowUpdate, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [← he]
  exact h₁.mul h₂

private theorem prescribeShear {c : R} (hc : IsUnit c) (s : Rˣ)
    (h : RingTernaryWord ζ 26 (rowUpdate c 0)) :
    RingTernaryWord ζ 28 (Matrix.transvection (0 : Fin 3) 1 (s : R)) := by
  obtain ⟨u, rfl⟩ := hc
  apply conjugateWord h ![s * u⁻¹, 1, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitDiag, rowUpdate, Matrix.transvection, Matrix.single_apply, Matrix.one_apply,
      mul_assoc]

/-- A prescribed unit shear uses twenty-eight monomial and forward ternary
Fourier slots, leaving the arbitrary contents of port two untouched. -/
theorem ringTernaryWord_unitShear (ζ a : R) (hζ : ζ^2 + ζ + 1 = 0)
    (h3 : IsUnit (3 : R)) (ha9 : a^9 = 1) (ha3 : IsUnit (a^3 - 1)) (s : Rˣ) :
    RingTernaryWord ζ 28 (Matrix.transvection (0 : Fin 3) 1 (s : R)) := by
  obtain ⟨ha, _, _, hA, hB⟩ := ternaryCycleUnits_of_cube_sub_one ha9 ha3
  obtain ⟨z, hz⟩ := (ternaryOmegaUnits hζ h3).1
  have hz₁ : IsUnit ((z : R) - 1) := hz ▸ (ternaryOmegaUnits hζ h3).2
  obtain ⟨A, hA⟩ := hA
  obtain ⟨B, hB⟩ := hB
  let t : R := (↑(A⁻¹) : R)
  let v : Rˣ := A * B⁻¹
  have ht : (1 + a^3) * t = 1 := by rw [← hA]; exact A.mul_inv
  have hv : (v : R) * ((1 + a^6) * t) = 1 := by
    rw [← hB]
    simp [t, v, mul_assoc]
  have hwS := changedCycleWord ha (ringTernaryWord_cycleSum ζ (a^2) hζ h3
    (by simpa only [← pow_mul] using (hB ▸ B.isUnit)))
  have hwI := ringTernaryWord_cycleInv ζ a t hζ h3 ht
  have hx : IsUnit (a^2 - a^5) := by
    rw [show a^2 - a^5 = -(a^2 * (a^3-1)) by ring]
    exact ((ha.pow 2).mul ha3).neg
  apply prescribeShear _ s (isolateRow (normalizeRow ht v hv hwS hwI) z)
  exact hz₁.mul ((v.isUnit.mul hx).mul A⁻¹.isUnit)

/-- Every shear coefficient over a semilocal ring is the sum of two units,
so two consecutive unit words suffice, including for a zero coefficient. -/
theorem ringTernaryWord_semilocalShear [Finite (MaximalSpectrum R)] (ζ a : R)
    (hζ : ζ^2 + ζ + 1 = 0) (h3 : IsUnit (3 : R)) (ha9 : a^9 = 1)
    (hres : ∀ m : MaximalSpectrum R, IsPrimitiveRoot (Ideal.Quotient.mk m.asIdeal a) 9)
    (s : R) : RingTernaryWord ζ 56 (Matrix.transvection (0 : Fin 3) 1 s) := by
  have ha3 := (ternaryCycleUnits ha9 hres).2.1
  obtain ⟨hω, hω₁⟩ := ternaryOmegaUnits hζ h3
  obtain ⟨t, ht, hu⟩ := exists_unit_split_of_third_residue hω hω₁ s
  have hw := (ringTernaryWord_unitShear ζ a hζ h3 ha9 ha3 ht.unit).mul
    (ringTernaryWord_unitShear ζ a hζ h3 ha9 ha3 hu.unit)
  rw [ht.unit_spec, hu.unit_spec, Matrix.transvection_mul_transvection_same (0 : Fin 3) 1 (by decide),
    show t + (s - t) = s by abel] at hw
  exact hw

/-- The field circuit charges at most twenty-eight Fourier calls for adding
port one into port zero, with port two restored. -/
theorem exists_ternaryFourierWord_unit_shear {K : Type*} [Field K] (ζ a : K)
    (hζ : ζ^2 + ζ + 1 = 0) (h3 : IsUnit (3 : K)) (ha9 : a^9 = 1)
    (ha3 : IsUnit (a^3 - 1)) :
    ∃ t ≤ 28, TernaryFourierWord ζ t (Matrix.transvection (0 : Fin 3) 1 (1 : K)) :=
  (ringTernaryWord_unitShear ζ a hζ h3 ha9 ha3 (1 : Kˣ)).fieldWord

end FiniteFourier
end LinearAlgebra
end OAI
