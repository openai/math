import OAI.Computability.NearSquareRoot.SynchronizedDilation
import OAI.Computability.NearSquareRoot.SynchronizedMatching
import Mathlib.Data.Matrix.Block

/-! # Three synchronized Walsh rounds for a dilation layer

In a pair of equally sized halves, the first coordinate of a product address
selects the half and the second coordinate labels a frequency. In this layout
the dilation is block diagonal over frequencies and all of its Walsh layers
are the same unconditional Walsh on the half bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair

variable {ι : Type*}

/-- The two borrowed halves become the two values of one designated address bit. -/
def dilationAddress : ι ⊕ ι ≃ Fin 2 × ι where
  toFun := Sum.elim (fun i => (0, i)) (fun i => (1, i))
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv s := by cases s <;> simp
  right_inv p := by rcases p with ⟨b, i⟩; fin_cases b <;> simp

variable [DecidableEq ι]

theorem dilation_blocks (z : ι → ℂ) :
    (dilation z).submatrix dilationAddress.symm dilationAddress.symm =
      blockDiagonal (fun i => pair (z i)) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  fin_cases b <;> fin_cases c <;>
    simp [dilation, dilationAddress, SynchronizedPair.pair, dilationOffDiagonal,
      blockDiagonal_apply, diagonal_apply]

/-- All paired frequencies use the same bit and the same normalized Walsh. -/
noncomputable def halfWalsh : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ := blockDiagonal fun _ => walsh

private def twoPhase (u v : ℂ) (b : Fin 2) : ℂ := if b = 0 then u else v

private theorem table_diag (u v : ℂ) :
    SynchronizedPair.diag u v = diagonal (twoPhase u v) := by
  ext b c
  fin_cases b <;> fin_cases c <;> simp [SynchronizedPair.diag, twoPhase]

private theorem table_norm (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (b : Fin 2) :
    ‖twoPhase u v b‖ = 1 := by unfold twoPhase; split <;> assumption

variable [Fintype ι]

/-- Explicit local formula for the six entries at a frequency. -/
noncomputable def dilationTable (z : ℂ) : Fin 6 → ℂ :=
  let t := dilationOffDiagonal z
  tableEntry ((w : ℂ) * (z + t)) ((w : ℂ) * (t - star z))

/-- Two entries in the six-element table give one phase on each half. -/
noncomputable def dilationPhase (z : ι → ℂ) (a b : Fin 6) (address : Fin 2 × ι) : ℂ :=
  twoPhase (dilationTable (z address.2) a) (dilationTable (z address.2) b) address.1

omit [Fintype ι] [DecidableEq ι] in
theorem dilationPhase_norm (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (a b : Fin 6) (address : Fin 2 × ι) : ‖dilationPhase z a b address‖ = 1 := by
  let h := (pair_eq_table (hz address.2)).1
  exact table_norm _ _ (h a) (h b) _

/-- The three phase tables have closed formulas in the original dilation multipliers. -/
theorem dilation_explicit_threeWalsh (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2) :
    (dilation z).submatrix dilationAddress.symm dilationAddress.symm =
      halfWalsh * diagonal (dilationPhase z 0 1) * halfWalsh * diagonal (dilationPhase z 2 3) *
        halfWalsh * diagonal (dilationPhase z 4 5) := by
  rw [dilation_blocks]
  have heq (i : ι) : pair (z i) =
      walsh * SynchronizedPair.diag (dilationTable (z i) 0) (dilationTable (z i) 1) *
      walsh * SynchronizedPair.diag (dilationTable (z i) 2) (dilationTable (z i) 3) *
      walsh * SynchronizedPair.diag (dilationTable (z i) 4) (dilationTable (z i) 5) :=
    (pair_eq_table (hz i)).2
  simp only [heq, table_diag, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_diagonal, halfWalsh]
  rfl

/-- The exponent-independent shape of the dilation pair layer. Its local input
multipliers need only satisfy the uniform modulus bound from the chirp estimate. -/
theorem dilation_threeWalsh (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2) :
    ∃ p q r : Fin 2 × ι → ℂ,
      (∀ t, ‖p t‖ = 1 ∧ ‖q t‖ = 1 ∧ ‖r t‖ = 1) ∧
      (dilation z).submatrix dilationAddress.symm dilationAddress.symm =
        halfWalsh * diagonal p * halfWalsh * diagonal q * halfWalsh * diagonal r := by
  rw [dilation_blocks]
  exact parallel_threeWalsh _ fun i => pair_threeWalsh (hz i)

/-- The adjoint dilation also uses the same three unconditional Walsh rounds,
with the phase tables chosen for the adjoint pair matrices. -/
theorem adjoint_dilation_threeWalsh (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2) :
    ∃ p q r : Fin 2 × ι → ℂ,
      (∀ t, ‖p t‖ = 1 ∧ ‖q t‖ = 1 ∧ ‖r t‖ = 1) ∧
      (dilation z)ᴴ.submatrix dilationAddress.symm dilationAddress.symm =
        halfWalsh * diagonal p * halfWalsh * diagonal q * halfWalsh * diagonal r := by
  rw [← Matrix.conjTranspose_submatrix, dilation_blocks, Matrix.blockDiagonal_conjTranspose]
  exact parallel_threeWalsh _ fun i => adjoint_pair_threeWalsh (hz i)

end ShortFourier

end NearSquareRoot
end Computability
end OAI
