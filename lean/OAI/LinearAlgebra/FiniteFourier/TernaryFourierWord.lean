import OAI.LinearAlgebra.FiniteFourier.PrimeSectors
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Lift a ternary Fourier word to a four-coordinate sector -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {K : Type*} [CommRing K]

/-- A word in scaled permutations and ternary Fourier matrices, counting its Fourier calls. -/
inductive TernaryFourierWord (ζ : K) : ℕ → Matrix (Fin 3) (Fin 3) K → Prop
  | monomial (p : Equiv.Perm (Fin 3)) (c : Fin 3 → K) :
      TernaryFourierWord ζ 0 (fun i j => if p i = j then c i else 0)
  | fourier : TernaryFourierWord ζ 1 (dftMatrix 3 ζ)
  | mul {m n : ℕ} {A B : Matrix (Fin 3) (Fin 3) K} :
      TernaryFourierWord ζ m A → TernaryFourierWord ζ n B → TernaryFourierWord ζ (m+n) (A*B)

/-- Adjoin one inactive coordinate to a ternary operation. -/
def padTernary (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) K :=
  Matrix.fromBlocks A 0 0 1

theorem padTernary_mul (A B : Matrix (Fin 3) (Fin 3) K) :
    padTernary (A*B) = padTernary A * padTernary B := by
  simp [padTernary, Matrix.fromBlocks_multiply]

private theorem scaledPerm_grid_free {I : Type*} [DecidableEq I]
    (p : Equiv.Perm I) (c : I → K) (n : ℕ) :
    RealizableAtMost (gridTensor (fun _ : Fin n => (fun i j : I => if p i = j then c i else 0))) 0 := by
  classical
  let q : Circuit K (Fin n → I) (Fin n → I) 0 :=
    ⟨.nil, fun i => .scaled (∏ k, c (i k)) (.inl (p ∘ i))⟩
  refine ⟨0, le_rfl, q, ?_⟩
  ext x y
  by_cases h : p ∘ x = y
  · subst y
    simp [q, Circuit.matrix, Circuit.eval, Readout.eval, gridTensor, Function.comp_def]
  · obtain ⟨i, hi⟩ : ∃ i, p (x i) ≠ y i := not_forall.mp fun h' => h (funext h')
    have hz : (∏ t, if p (x t) = y t then c (x t) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    simpa [q, Circuit.matrix, Circuit.eval, Readout.eval, gridTensor, Pi.single_apply, h,
      eq_comm] using hz.symm

/-- Tensor powers of a padded word retain its Fourier-call count. All other
stages use only free rewiring and output scaling. -/
theorem TernaryFourierWord.padded_cost {ζ : K} {t : ℕ} {A : Matrix (Fin 3) (Fin 3) K}
    (hw : TernaryFourierWord ζ t A) (n : ℕ) :
    RealizableAtMost (gridTensor (fun _ : Fin n => padTernary A))
      (t * complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ))) := by
  induction hw with
  | monomial p c =>
    let q := p.sumCongr (Equiv.refl Unit)
    let a : Fin 3 ⊕ Unit → K := Sum.elim c (fun _ => 1)
    have he : padTernary (fun i j => if p i = j then c i else 0) =
        fun i j => if q i = j then a i else 0 := by
      ext (i|i) (j|j) <;> simp [padTernary, Matrix.fromBlocks, q, a]
    simpa only [he, zero_mul] using scaledPerm_grid_free q a n
  | fourier => simpa [ternarySectorStage, padTernary] using
      realizableAtMost_complexity (gridTensor (fun _ : Fin n => ternarySectorStage ζ))
  | mul _ _ ihA ihB =>
    simp only [padTernary_mul, gridTensor_mul, add_mul]
    exact ihA.mul ihB

end

end FiniteFourier
end LinearAlgebra
end OAI
