import OAI.LinearAlgebra.FiniteFourier.TernaryFourierWord

/-! # Ternary Fourier words over a protected coefficient ring

Each monomial layer is an invertible scaled permutation. Both monomial and
Fourier layers count towards the length, which also bounds the number of
Fourier calls after any specialization to a field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R]

/-- The positive-sign width-three Fourier matrix over a commutative ring. -/
def ringTernaryDFT (ζ : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => ζ ^ (i.val * j.val)

/-- Exact width-three word with the total number of slots. -/
inductive RingTernaryWord (ζ : R) : ℕ → Matrix (Fin 3) (Fin 3) R → Prop
  | id : RingTernaryWord ζ 0 1
  | monomial (p : Equiv.Perm (Fin 3)) (c : Fin 3 → Rˣ) :
      RingTernaryWord ζ 1 (fun i j => if p i = j then (c i : R) else 0)
  | fourier : RingTernaryWord ζ 1 (ringTernaryDFT ζ)
  | mul {m n : ℕ} {A B : Matrix (Fin 3) (Fin 3) R} :
      RingTernaryWord ζ m A → RingTernaryWord ζ n B → RingTernaryWord ζ (m+n) (A*B)

variable {ζ : R}

theorem RingTernaryWord.diagonal (c : Fin 3 → Rˣ) :
    RingTernaryWord ζ 1 (Matrix.diagonal (fun i => (c i : R))) := by
  exact RingTernaryWord.monomial (ζ := ζ) (Equiv.refl _) c

theorem RingTernaryWord.permutation (p : Equiv.Perm (Fin 3)) :
    RingTernaryWord ζ 1 (fun i j => if p i = j then (1 : R) else 0) :=
  RingTernaryWord.monomial p (fun _ => 1)

/-- A coefficient map preserves each slot. The padded sector construction
charges only the Fourier calls. -/
theorem RingTernaryWord.mapFourierWord {n : ℕ} {A : Matrix (Fin 3) (Fin 3) R}
    (h : RingTernaryWord ζ n A) {K : Type*} [CommRing K] (φ : R →+* K) :
    ∃ t ≤ n, TernaryFourierWord (φ ζ) t (A.map φ) := by
  induction h with
  | id =>
    refine ⟨0, le_rfl, ?_⟩
    have he : (1 : Matrix (Fin 3) (Fin 3) R).map φ =
        fun i j => if (Equiv.refl (Fin 3)) i = j then (1 : K) else 0 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.map_apply, h]
    rw [he]
    exact TernaryFourierWord.monomial _ (fun _ => 1)
  | monomial p c =>
    refine ⟨0, by decide, ?_⟩
    have he : Matrix.map (fun i j => if p i = j then (c i : R) else 0) φ =
        fun i j => if p i = j then φ (c i) else 0 := by
      ext i j
      change φ (if p i = j then (c i : R) else 0) = if p i = j then φ (c i) else 0
      split <;> simp
    rw [he]
    exact TernaryFourierWord.monomial _ _
  | fourier =>
    refine ⟨1, le_rfl, ?_⟩
    convert TernaryFourierWord.fourier (ζ := φ ζ) using 2
    ext i j
    simp [ringTernaryDFT, dftMatrix]
  | mul h₁ h₂ ih₁ ih₂ =>
    obtain ⟨u, hu, hU⟩ := ih₁
    obtain ⟨v, hv, hV⟩ := ih₂
    refine ⟨u+v, Nat.add_le_add hu hv, ?_⟩
    rw [Matrix.map_mul]
    exact hU.mul hV

/-- Dropping the monomial slots from the charged length is valid over the
original coefficient ring. -/
theorem RingTernaryWord.fourierWord {n : ℕ} {A : Matrix (Fin 3) (Fin 3) R}
    (h : RingTernaryWord ζ n A) : ∃ t ≤ n, TernaryFourierWord ζ t A := by
  simpa using h.mapFourierWord (RingHom.id R)

/-- Specialization to a field preserves the Fourier-call estimate. -/
theorem RingTernaryWord.toFieldWord {n : ℕ} {A : Matrix (Fin 3) (Fin 3) R}
    (h : RingTernaryWord ζ n A) {K : Type*} [Field K] (φ : R →+* K) :
    ∃ t ≤ n, TernaryFourierWord (φ ζ) t (A.map φ) :=
  h.mapFourierWord φ

/-- When the starting ring is a field, no coefficient map is needed. -/
theorem RingTernaryWord.fieldWord {K : Type*} [Field K] {ω : K}
    {n : ℕ} {A : Matrix (Fin 3) (Fin 3) K} (h : RingTernaryWord ω n A) :
    ∃ t ≤ n, TernaryFourierWord ω t A := by
  exact h.fourierWord

end FiniteFourier
end LinearAlgebra
end OAI
