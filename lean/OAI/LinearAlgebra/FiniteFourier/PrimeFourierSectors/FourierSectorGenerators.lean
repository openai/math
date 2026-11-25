import OAI.LinearAlgebra.FiniteFourier.FourierSectors

/-! # Fourier sectors for elementary tensor factors

An identity coordinate is a zero-digit sector. A padded Fourier transform has
one extra sector carrying a single digit, together with the identity sectors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeFourierSectors

variable {R : Type*} [CommRing R]

/-- Decompose an identity matrix into singleton Fourier blocks. -/
def one (p : ℕ) (ζ : R) (I : Type) [Fintype I] [DecidableEq I] :
    PrimeFourierSectors p ζ (1 : Matrix I I R) where
  B := I
  digits := fun _ => 0
  e := {
    toFun := fun ⟨b, _⟩ => b
    invFun := fun b => ⟨b, Fin.elim0⟩
    left_inv := fun ⟨b, x⟩ => congrArg (Sigma.mk b) (Subsingleton.elim _ _)
    right_inv := fun _ => rfl }
  block := by
    ext ⟨a, x⟩ ⟨b, y⟩
    by_cases h : a = b
    · subst b
      rw [Matrix.blockDiagonal'_apply_eq]
      simp
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      simp [h]
  one_digit := fun _ => Nat.zero_le _

private def paddedDigits {J : Type} : Option J → ℕ
  | none => 1
  | some _ => 0

private def paddedEquiv (p : ℕ) (J : Type) :
    (Σ b : Option J, Fin (paddedDigits b) → Fin p) ≃ (Fin p ⊕ J) where
  toFun
    | ⟨none, x⟩ => Sum.inl (x (0 : Fin 1))
    | ⟨some j, _⟩ => Sum.inr j
  invFun
    | Sum.inl x => ⟨none, fun _ => x⟩
    | Sum.inr j => ⟨some j, Fin.elim0⟩
  left_inv := by
    rintro ⟨_ | j, x⟩
    · apply congrArg (Sigma.mk none)
      funext i
      exact congrArg x (Subsingleton.elim (0 : Fin 1) i)
    · apply congrArg (Sigma.mk (some j))
      exact funext fun i => Fin.elim0 i
  right_inv := by rintro (x | j) <;> rfl

/-- One radix-`p` Fourier block, with any finite number of fixed coordinates. -/
def padded (p : ℕ) (ζ : R) (J : Type) [Fintype J] [DecidableEq J] :
    PrimeFourierSectors p ζ
      (Matrix.fromBlocks (dftMatrix p ζ) 0 0 (1 : Matrix J J R)) where
  B := Option J
  digits := paddedDigits
  e := paddedEquiv p J
  block := by
    ext ⟨a, x⟩ ⟨b, y⟩
    cases a <;> cases b
    case none.none =>
      rw [Matrix.blockDiagonal'_apply_eq]
      change ζ ^ ((x (0 : Fin 1)).val * (y (0 : Fin 1)).val) = primeTransform p 1 ζ x y
      simp [primeTransform]
    case none.some j =>
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (show (none : Option J) ≠ some j by simp)]
      rfl
    case some.none i =>
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (show some i ≠ (none : Option J) by simp)]
      rfl
    case some.some i j =>
      by_cases h : i = j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        change (1 : Matrix J J R) i i = primeTransform p 0 ζ x y
        simp [primeTransform]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (mt Option.some.inj h)]
        change (1 : Matrix J J R) i j = 0
        simp [h]
  one_digit := by rintro (_ | _) <;> simp [paddedDigits]

/-- Transport all sectors by the same relabeling of input and output wires. -/
def reindex {p : ℕ} {ζ : R} {I J : Type} {A : Matrix I I R}
    (h : PrimeFourierSectors p ζ A) (e : I ≃ J) :
    PrimeFourierSectors p ζ (Matrix.reindex e e A) where
  B := h.B
  digits := h.digits
  e := h.e.trans e
  block := by
    ext i j
    simpa using congrFun (congrFun h.block i) j
  one_digit := h.one_digit

/-- An entire radix-`p` Fourier matrix is one active digit. -/
def full (p : ℕ) (ζ : R) : PrimeFourierSectors p ζ (dftMatrix p ζ) where
  B := Unit
  digits := fun _ => 1
  e := {
    toFun := fun t => t.2 0
    invFun := fun i => ⟨(), fun _ => i⟩
    left_inv := by
      rintro ⟨⟨⟩, x⟩
      apply congrArg (Sigma.mk ())
      exact funext fun i => congrArg x (Subsingleton.elim (0 : Fin 1) i)
    right_inv := fun _ => rfl }
  block := by
    ext ⟨⟨⟩, x⟩ ⟨⟨⟩, y⟩
    rw [Matrix.blockDiagonal'_apply_eq]
    change ζ ^ ((x 0).val * (y 0).val) = primeTransform p 1 ζ x y
    simp [primeTransform]
  one_digit := fun _ => le_rfl

end PrimeFourierSectors

end FiniteFourier
end LinearAlgebra
end OAI
