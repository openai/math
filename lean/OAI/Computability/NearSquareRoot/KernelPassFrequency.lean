import OAI.Computability.NearSquareRoot.KernelPassMatrixTable
import OAI.Computability.NearSquareRoot.KernelPassHermite

/-! # Frequency coordinates for streamed repair stages

The exact two-bit rational Walsh kernel is an involution. Tensoring first
over physical axes and then over columns gives a single involution on rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open Matrix Finset SynchronizedPadding

variable {A h n i o m : ℕ}

def pairWalsh : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℚ := pairEntry

def columnWalsh (A : ℕ) : Matrix (Column A) (Column A) ℚ :=
  tensorMatrix fun _ : Fin A => pairWalsh

def walshMatrix (A h : ℕ) : Matrix (Addr A h) (Addr A h) ℚ :=
  tensorMatrix fun _ : Fin h => columnWalsh A

theorem pairEntry_mul_self : pairWalsh * pairWalsh = 1 := by
  let e := finTwoArrowEquiv (ZMod 2)
  apply (Matrix.reindexRingEquiv ℚ e).injective
  rw [map_mul, map_one]
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ b : Fin 2, ∑ c : Fin 2, _) = _
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [e, Matrix.reindexRingEquiv, Matrix.reindexAddEquiv, Matrix.reindex, Matrix.submatrix,
      finTwoArrowEquiv, pairWalsh, pairEntry, Matrix.one_apply] <;> simp +decide <;> norm_num

theorem walshMatrix_mul_self (A h : ℕ) : walshMatrix A h * walshMatrix A h = 1 := by
  have hc : columnWalsh A * columnWalsh A = 1 := by
    rw [columnWalsh, ← tensorMatrix_mul (fun _ : Fin A => pairWalsh) (fun _ : Fin A => pairWalsh)]
    simp only [pairEntry_mul_self, tensorMatrix_one]
  rw [walshMatrix, ← tensorMatrix_mul]
  simp only [hc, tensorMatrix_one]

def frequency (x : Bank A h n) : Bank A h n := fun b => walshMatrix A h *ᵥ x b

@[simp] theorem frequency_frequency (x : Bank A h n) : frequency (frequency x) = x := by
  funext i
  simp [frequency, Matrix.mulVec_mulVec, walshMatrix_mul_self]

theorem applyAt_convertBank (x : Bank A h n) : (convertBank A n).applyAt h x = frequency x := by
  funext i y
  rw [convertBank, applyAt_perRow]
  simp [applyAt, fullConversion_correct A h, target, frequency, walshMatrix, columnWalsh, pairWalsh,
    tensorMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem frequency_spectralTable (test : Column A → Fin m → ZMod 2)
    (c : (Fin m → ZMod 2) → Fin o → Fin i → Coefficient)
    (x : Bank A h i) (b : Fin o) (y : Addr A h) :
    frequency ((spectralTable test c).applyAt h x) b y =
      ∑ a, value (c (∑ t, test (y t)) b a) * frequency x a y := by
  rw [spectralTable, applyAt_seq, applyAt_seq, applyAt_convertBank, applyAt_convertBank,
    frequency_frequency, applyAt_matrixTable]

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
