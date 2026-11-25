import OAI.LinearAlgebra.FiniteFourier.PrimeMatrixRoot
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowRows

/-! # The common-width pencil acting on repair rows

Each shift has a full block of independent input rows. In the spectral basis
the same specialized matrix acts on the block at each step.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix MvPolynomial

variable {ℓ m b h : ℕ} [NeZero ℓ] {K V ν : Type*} [CommRing K] [AddCommGroup V] [Module K V]
variable {ζ : K}

/-- Pack the shift and the clock digit vector using the row numbering of the repair program. -/
def clockShiftRowEquivFin (ℓ m b h : ℕ) [NeZero ℓ] :
    ((Fin m → ZMod ℓ) × (Fin h → Fin b)) ≃ Fin (ℓ ^ m * b ^ h) :=
  let clock : (Fin h → Fin b) ≃ Fin (b ^ h) := Fintype.equivFinOfCardEq (by simp)
  ((Equiv.refl _).prodCongr clock).trans (shiftRowEquivFin ℓ m (b ^ h))

variable (hζ : IsPrimitiveRoot ζ ℓ) (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ)
variable (L : (Fin m → ZMod ℓ) →
  Matrix (Fin h → Fin b) (Fin h → Fin b) (MvPolynomial (Fin m × ZMod ℓ) K))

/-- Apply one specialized pencil to each shift block in the spectral basis. -/
def countPencilStep (x : Fin (ℓ ^ m * b ^ h) → V) (i : Fin (ℓ ^ m * b ^ h)) : V :=
  let e := clockShiftRowEquivFin ℓ m b h
  let r := e.symm i
  S.symm fun ω => (((L r.1).map (eval (queryPowerValues hζ (k ω)))) *ᵥ
    fun a => S (x (e (r.1, a))) ω) r.2

/-- In a fixed shift block, repeated pencil steps act by the corresponding matrix power. -/
theorem countPencilStep_iterate_block (n : ℕ) (x : Fin (ℓ ^ m * b ^ h) → V)
    (β : Fin m → ZMod ℓ) (ω : ν) :
    (fun a => S ((countPencilStep hζ S k L)^[n] x (clockShiftRowEquivFin ℓ m b h (β, a))) ω) =
      ((L β).map (eval (queryPowerValues hζ (k ω)))) ^ n *ᵥ
        fun a => S (x (clockShiftRowEquivFin ℓ m b h (β, a))) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih]
    funext a
    simp only [Function.iterate_succ_apply', countPencilStep, Equiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]

/-- After `b` stages, each scalar predictor multiplies every row in its own shift block. -/
theorem countPencilStep_iterate_predictor {u : ℤ} {D : ℕ}
    (hL : ∀ β, (L β) ^ b = countPredictor hζ β u D • 1)
    (x : Fin (ℓ ^ m * b ^ h) → V) (i : Fin (ℓ ^ m * b ^ h)) (ω : ν) :
    S ((countPencilStep hζ S k L)^[b] x i) ω =
      eval (queryPowerValues hζ (k ω))
        (countPredictor hζ ((shiftRowEquivFin ℓ m (b ^ h)).symm i).1 u D) * S (x i) ω := by
  obtain ⟨⟨β, a⟩, rfl⟩ := (clockShiftRowEquivFin ℓ m b h).surjective i
  have hact := congrFun (countPencilStep_iterate_block hζ S k L b x β ω) a
  rw [specialize_matrix_root _ (hL β), Matrix.smul_mulVec, Matrix.one_mulVec] at hact
  simpa [clockShiftRowEquivFin] using hact

end

end

end FiniteFourier
end LinearAlgebra
end OAI
