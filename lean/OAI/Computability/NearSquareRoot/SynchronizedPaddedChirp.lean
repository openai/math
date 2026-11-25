import OAI.Computability.NearSquareRoot.SynchronizedChirp
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # The first Bluestein compression

The long circulant is the zero extension of the short quadratic chirp. If
`2a - 1 ≤ r`, no two signed differences of occupied coordinates collide.
The compression to the first `a` coordinates, between the two chirp phase
diagonals, gives the exact positive-sign normalized Fourier matrix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix Finset
open scoped Matrix

noncomputable section

/-- Push the signed difference kernel into its cyclic array of length `r`.
An unoccupied residue receives zero by the empty sum. -/
def paddedKernel (a r : ℕ) (t : Fin r) : ℂ :=
  ∑ h ∈ Ioo (-(a : ℤ)) (a : ℤ),
    if h % (r : ℤ) = t.val then
      (Real.sqrt a : ℂ)⁻¹ * phase (-((h : ℝ)^2) / (2 * a)) else 0

private theorem window_mod_injective {a r : ℕ} (hr : 2*a-1 ≤ r)
    {x y : ℤ} (hx : x ∈ Ioo (-(a : ℤ)) (a : ℤ)) (hy : y ∈ Ioo (-(a : ℤ)) (a : ℤ))
    (h : x % (r : ℤ) = y % (r : ℤ)) : x = y := by
  rw [mem_Ioo] at hx hy
  have hxy : x ≡ y [ZMOD (r : ℤ)] := h
  rcases lt_trichotomy x y with hlt | he | hgt
  · have := Int.le_of_dvd (by omega : 0 < y - x) hxy.dvd
    omega
  · exact he
  · have := Int.le_of_dvd (by omega : 0 < x - y) hxy.symm.dvd
    omega

private theorem val_sub_emod {r : ℕ} (i j : Fin r) :
    ((i - j).val : ℤ) = ((i.val : ℤ) - j.val) % r := by
  have h₁ := i.isLt
  have h₂ := j.isLt
  rw [Fin.intCast_val_sub_eq_sub_add_ite]
  split_ifs with h
  · have := Fin.le_def.mp h
    simp [Int.emod_eq_of_lt (by omega : 0 ≤ (i.val : ℤ) - j.val) (by omega : (i.val : ℤ) - j.val < r)]
  · have hh : i.val < j.val := Fin.lt_def.mp (lt_of_not_ge h)
    have hpos : 0 ≤ (i.val : ℤ) - j.val + r := by omega
    have hlt : (i.val : ℤ) - j.val + r < r := by omega
    rw [← Int.add_emod_right ((i.val : ℤ) - j.val) (r : ℤ), Int.emod_eq_of_lt hpos hlt]

/-- The long circulant evaluated at two occupied positions has the signed
integer difference prescribed by the short transform. -/
theorem paddedKernel_sub {a r : ℕ} (hr : 2*a-1 ≤ r) (har : a ≤ r) (i j : Fin a) :
    paddedKernel a r ((i.castLE har) - (j.castLE har)) =
      (Real.sqrt a : ℂ)⁻¹ * phase (-(((i.val : ℤ) - j.val : ℤ) : ℝ)^2 / (2*a)) := by
  let d : ℤ := i.val - (j.val : ℤ)
  have hd : d ∈ Ioo (-(a : ℤ)) (a : ℤ) := by
    have := i.isLt
    have := j.isLt
    simp only [mem_Ioo, d]
    omega
  have hmod : (((i.castLE har - j.castLE har).val : ℤ)) = d % r := val_sub_emod _ _
  rw [paddedKernel, Finset.sum_eq_single d]
  · simp [hmod, d]
  · intro h hh hne
    apply ite_eq_right
    rw [hmod]
    exact fun eq => hne (window_mod_injective hr hh hd eq)
  · exact fun h => (h hd).elim

/-- Positive quadratic phases at both ends of the compression. -/
def bluesteinDiagonal (a : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  diagonal (fun i => phase ((i.val : ℝ)^2 / (2*a)))

/-- Exact normalized Bluestein transform, with a cyclic zero-padded kernel
and the physical restriction to the first coordinates. -/
theorem normalizedFourier_padded {a r : ℕ} (ha : 0 < a) (hr : 2*a-1 ≤ r) :
    let f := Fin.castLE (show a ≤ r by omega)
    bluesteinDiagonal a * (circulant (paddedKernel a r)).submatrix f f * bluesteinDiagonal a =
      normalizedFourier a := by
  dsimp only
  ext i j
  simp only [bluesteinDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.submatrix_apply, circulant_apply, normalizedFourier]
  rw [paddedKernel_sub hr]
  push_cast
  rw [show ∀ A B C s : ℂ, A * (s * B) * C = s * ((A * B) * C) by intros; ring,
    ← phase_add, ← phase_add]
  congr 2
  field_simp
  ring

/-- The isometric inclusion of the occupied coordinates into the padded array. -/
def firstCoords {a r : ℕ} (har : a ≤ r) : Matrix (Fin r) (Fin a) ℂ :=
  fun i j => if i = j.castLE har then 1 else 0

/-- Zero extension followed by restriction to the first coordinates is the
principal submatrix operation used above. -/
theorem firstCoords_compression {a r : ℕ} (har : a ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) :
    (firstCoords har)ᴴ * M * firstCoords har = M.submatrix (Fin.castLE har) (Fin.castLE har) := by
  ext i j
  classical
  simp [Matrix.mul_apply, firstCoords, Matrix.conjTranspose_apply, mul_ite, ite_mul]

theorem firstCoords_isometry {a r : ℕ} (har : a ≤ r) :
    (firstCoords har)ᴴ * firstCoords har = 1 := by
  have h := firstCoords_compression har 1
  rw [Matrix.mul_one] at h
  rw [h]
  apply Matrix.submatrix_one
  exact fun _ _ e => Fin.ext (congrArg (fun k : Fin r => k.val) e)

theorem bluesteinDiagonal_isometry (a : ℕ) :
    (bluesteinDiagonal a)ᴴ * bluesteinDiagonal a = 1 := by
  rw [bluesteinDiagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  change (starRingEnd ℂ) (phase _) * phase _ = 1
  rw [phase_conj]
  exact inv_mul_cancel₀ (Complex.exp_ne_zero _)

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
