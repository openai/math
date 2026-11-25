import OAI.LinearAlgebra.FiniteFourier.PrimeFourierSectors.FourierSectorGenerators

/-! # Extending a Fourier-sector decomposition by idle coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeFourierSectors

variable {R : Type*} [CommRing R] {p : ℕ} {ζ : R} {I : Type} {A : Matrix I I R}

/-- Adjoin identity wires to a matrix with a sector decomposition. Each new
wire is a separate zero-digit sector. -/
def addIdentity (h : PrimeFourierSectors p ζ A) (J : Type) [Fintype J] [DecidableEq J] :
    PrimeFourierSectors p ζ (Matrix.fromBlocks A 0 0 (1 : Matrix J J R)) where
  B := h.B ⊕ J
  digits := Sum.elim h.digits (fun _ => 0)
  e := (Equiv.sumSigmaDistrib (fun b => Fin (Sum.elim h.digits (fun _ : J => 0) b) → Fin p)).trans
    (Equiv.sumCongr h.e (one p ζ J).e)
  block := by
    ext ⟨a, x⟩ ⟨b, y⟩
    cases a <;> cases b
    case inl.inl a b =>
      by_cases h' : a = b
      · subst b
        rw [Matrix.blockDiagonal'_apply_eq]
        change Fin (h.digits a) → Fin p at x y
        exact (congrFun₂ h.block ⟨a, x⟩ ⟨a, y⟩).trans (Matrix.blockDiagonal'_apply_eq ..)
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (mt Sum.inl.inj h')]
        change Fin (h.digits a) → Fin p at x
        change Fin (h.digits b) → Fin p at y
        exact (congrFun₂ h.block ⟨a, x⟩ ⟨b, y⟩).trans (Matrix.blockDiagonal'_apply_ne _ _ _ h')
    case inl.inr a b =>
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Sum.inl_ne_inr)]
      rfl
    case inr.inl a b =>
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Sum.inr_ne_inl)]
      rfl
    case inr.inr a b =>
      change (1 : Matrix J J R) a b = _
      by_cases h' : a = b
      · subst b
        rw [Matrix.blockDiagonal'_apply_eq]
        change (1 : Matrix J J R) a a = primeTransform p 0 ζ x y
        simp [primeTransform]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (mt Sum.inr.inj h')]
        simp [h']
  one_digit := by rintro (b | j); exacts [h.one_digit b, Nat.zero_le _]

end PrimeFourierSectors

end FiniteFourier
end LinearAlgebra
end OAI
