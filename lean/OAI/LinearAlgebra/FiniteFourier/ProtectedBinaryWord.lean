import OAI.LinearAlgebra.FiniteFourier.ProtectedShears
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Three forward binary kernel calls for a unit shear

The exact word in the two-coordinate kernel uses unit diagonal matrices between
forward calls. The eighth-root choice keeps all diagonal entries invertible
in the protected coefficient ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R]

/-- The integral two-coordinate Hadamard matrix. -/
def compilerHadamard (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, -1]

/-- The binary kernel in the paper, with `h = 1/2` and `i² = -1`. -/
def protectedBinaryKernel (h i : R) : Matrix (Fin 2) (Fin 2) R :=
  !![(1+i)*h, (1-i)*h; (1-i)*h, (1+i)*h]

/-- One invertible diagonal on a pair of registers. -/
def binaryUnitDiagonal (u v : Rˣ) : Matrix (Fin 2) (Fin 2) R := diagonal ![(u : R), (v : R)]

/-- An alternating matrix word containing exactly `n` forward calls to `C`,
with an invertible diagonal before, between and after the calls. -/
inductive ForwardBinaryWord (C : Matrix (Fin 2) (Fin 2) R) :
    ℕ → Matrix (Fin 2) (Fin 2) R → Prop where
  | diagonal (u v : Rˣ) : ForwardBinaryWord C 0 (binaryUnitDiagonal u v)
  | step {n A} (u v : Rˣ) (h : ForwardBinaryWord C n A) :
      ForwardBinaryWord C (n+1) (binaryUnitDiagonal u v * C * A)

private theorem binaryUnitDiagonal_mul (u v s t : Rˣ) :
    binaryUnitDiagonal u v * binaryUnitDiagonal s t = binaryUnitDiagonal (u*s) (v*t) := by
  rw [binaryUnitDiagonal, binaryUnitDiagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem ForwardBinaryWord.leftDiagonal {C A : Matrix (Fin 2) (Fin 2) R} {n}
    (h : ForwardBinaryWord C n A) (s t : Rˣ) :
    ForwardBinaryWord C n (binaryUnitDiagonal s t * A) := by
  cases h with
  | diagonal => rw [binaryUnitDiagonal_mul]; exact .diagonal ..
  | step u v h =>
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, binaryUnitDiagonal_mul]
    exact .step _ _ h

theorem ForwardBinaryWord.mul {C A B : Matrix (Fin 2) (Fin 2) R} {n m}
    (hA : ForwardBinaryWord C n A) (hB : ForwardBinaryWord C m B) :
    ForwardBinaryWord C (n+m) (A * B) := by
  induction hA with
  | diagonal u v => simpa using hB.leftDiagonal u v
  | step u v _ ih =>
    rw [Nat.succ_add, Matrix.mul_assoc]
    exact .step u v ih

/-- The exact triangular identity in equation `poly:eq:binary-shear`.
Here `d` denotes the inverse of `z - 1`. -/
theorem protectedBinary_triangular (z d : R) (hd : (z-1)*d = 1) :
    compilerHadamard R * diagonal ![z, 1] * compilerHadamard R *
      diagonal ![-(z+1)*d, 1] * compilerHadamard R =
        !![-4*z*d, -2*(z^2+1)*d; 0, -2*(z+1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, compilerHadamard] <;>
    norm_num
  · linear_combination (1-z)*hd
  · linear_combination (z-1)*hd
  · linear_combination (-z-1)*hd
  · linear_combination (-z-1)*hd

/-- At an eighth root, all three upper entries are units, and the triangular matrix
in the certificate is invertible. -/
theorem protectedBinary_triangular_isUnit [IsDomain R] {ζ d : R}
    (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) (hd : (ζ-1)*d = 1) :
    IsUnit (-4*ζ*d) ∧ IsUnit (-2*(ζ^2+1)*d) ∧ IsUnit (-2*(ζ+1)) ∧
      IsUnit (compilerHadamard R * diagonal ![ζ, 1] * compilerHadamard R *
        diagonal ![-(ζ+1)*d, 1] * compilerHadamard R) := by
  obtain ⟨hz, _, hp, hs⟩ := compiler_eighthRoot_units hζ h₂
  have hu : IsUnit d := isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hd⟩
  have h4 : IsUnit (4 : R) := by convert h₂.pow 2 using 1; norm_num
  have ha := (h4.neg.mul hz).mul hu
  have hc := h₂.neg.mul hp
  refine ⟨ha, (h₂.neg.mul hs).mul hu, hc, ?_⟩
  rw [protectedBinary_triangular ζ d hd, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
  simpa only [mul_zero, sub_zero] using ha.mul hc

/-- A triangular matrix with all three upper entries units can be scaled on its two
sides to an upper shear with any prescribed unit coefficient. -/
private theorem ForwardBinaryWord.triangularToShear {C : Matrix (Fin 2) (Fin 2) R}
    {n} (a b c t : Rˣ) (h : ForwardBinaryWord C n !![(a : R), (b : R); 0, (c : R)]) :
    ForwardBinaryWord C n !![1, (t : R); 0, 1] := by
  have hw := (h.leftDiagonal (t*b⁻¹) c⁻¹).mul (.diagonal (a⁻¹*b*t⁻¹) 1)
  change ForwardBinaryWord C n _ at hw
  convert hw using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryUnitDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc,
      mul_left_comm, mul_comm] <;>
    simp only [← Units.val_mul]
  · change ((1 : Rˣ) : R) = _
    apply congrArg Units.val
    calc
      1 = (a*a⁻¹)*(b*b⁻¹)*(t*t⁻¹) := by simp
      _ = _ := by ac_rfl
  · apply congrArg Units.val
    calc
      t = t*(b*b⁻¹) := by simp
      _ = _ := by ac_rfl

/-- Diagonal equivalence between the Hadamard and binary kernels, using `i²=-1`. -/
private theorem hadamard_oneCall {i h : R} (hi : i^2 = -1) (u a : Rˣ)
    (hu : (u : R) = i) (ha : (a : R) = (1+i)*h) :
    ForwardBinaryWord (protectedBinaryKernel h i) 1 (compilerHadamard R) := by
  have hmat : binaryUnitDiagonal 1 u * protectedBinaryKernel h i * binaryUnitDiagonal 1 u =
      binaryUnitDiagonal a a * compilerHadamard R := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [binaryUnitDiagonal, protectedBinaryKernel, compilerHadamard, diagonal_mul, mul_diagonal,
        hu, ha]
    · linear_combination -h*hi
    · linear_combination -h*hi
    · linear_combination (1+i)*h*hi
  have hw : ForwardBinaryWord (protectedBinaryKernel h i) 1
      (binaryUnitDiagonal 1 u * protectedBinaryKernel h i * binaryUnitDiagonal 1 u) :=
    .step _ _ (.diagonal _ _)
  rw [hmat] at hw
  have he := hw.leftDiagonal a⁻¹ a⁻¹
  rw [← Matrix.mul_assoc, binaryUnitDiagonal_mul, inv_mul_cancel, show binaryUnitDiagonal
    (1 : Rˣ) 1 = 1 by ext i j; fin_cases i <;> fin_cases j <;>
      simp [binaryUnitDiagonal, one_apply], Matrix.one_mul] at he
  exact he

/-- Three forward calls to the binary kernel suffice for every unit upper shear.
The parameter `ζ` is the primitive eighth root and `ζ²` is the paper's `i`. -/
theorem protectedBinary_unitShear_word [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 8)
    (h₂ : IsUnit (2 : R)) (t : Rˣ) : ForwardBinaryWord
      (protectedBinaryKernel (↑h₂.unit⁻¹ : R) (ζ^2)) 3 !![1, (t : R); 0, 1] := by
  obtain ⟨hz, hm, hp, hs⟩ := compiler_eighthRoot_units hζ h₂
  let d : Rˣ := hm.unit⁻¹
  have hd : (ζ-1) * (d : R) = 1 := by rw [← hm.unit_spec]; exact hm.unit.mul_inv
  let half : R := (h₂.unit⁻¹ : Rˣ)
  let C := protectedBinaryKernel half (ζ^2)
  have hih : (ζ^2)^2 = -1 := by
    rw [← pow_mul]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 8) hζ (show 8 = 4*2 by decide)).eq_neg_one_of_two_right
  have hu : IsUnit (ζ^2) := hz.pow 2
  have ha : IsUnit ((1+ζ^2)*half) := (by simpa [add_comm] using hs : IsUnit (1+ζ^2)).mul
    (h₂.unit⁻¹).isUnit
  have hH : ForwardBinaryWord C 1 (compilerHadamard R) :=
    hadamard_oneCall hih hu.unit ha.unit hu.unit_spec ha.unit_spec
  have hmid₁ : ForwardBinaryWord C 0 (diagonal ![ζ, 1]) := by
    simpa [binaryUnitDiagonal] using (ForwardBinaryWord.diagonal (C := C) hz.unit 1)
  have hmidUnit := hp.neg.mul d.isUnit
  have hmid₂ : ForwardBinaryWord C 0 (diagonal ![-(ζ+1)*(d : R), 1]) := by
    simpa [binaryUnitDiagonal] using (ForwardBinaryWord.diagonal (C := C) hmidUnit.unit 1)
  have hall := (((hH.mul hmid₁).mul hH).mul hmid₂).mul hH
  rw [protectedBinary_triangular ζ d hd] at hall
  obtain ⟨hA, hB, hD, _⟩ := protectedBinary_triangular_isUnit hζ h₂ hd
  apply ForwardBinaryWord.triangularToShear hA.unit hB.unit hD.unit t
  simpa only [IsUnit.unit_spec] using hall

/-- Six forward calls give every upper shear, including the zero coefficient,
over a semilocal protected coefficient domain. -/
theorem protectedBinary_shear_word [IsDomain R] [Finite (MaximalSpectrum R)]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) (μ : R) :
    ForwardBinaryWord (protectedBinaryKernel (↑h₂.unit⁻¹ : R) (ζ^2)) 6 !![1, μ; 0, 1] := by
  obtain ⟨t, ht, hv⟩ := exists_unit_split h₂ μ
  have hw := (protectedBinary_unitShear_word hζ h₂ ht.unit).mul
    (protectedBinary_unitShear_word hζ h₂ hv.unit)
  convert hw using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp

end FiniteFourier
end LinearAlgebra
end OAI
