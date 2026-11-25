import OAI.Computability.BorderVNP.ResidueBox
import Mathlib.Data.Fintype.BigOperators

/-! # Finite indexing of the Laurent monomial tests in §10.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueBox

variable {σ : Type*}

/-- Index the signed parameter exponent by shifting it up by `H`, and retain the
nonnegative polynomial exponents as bounded natural numbers. -/
def boxEquiv (H : ℕ) :
    {e : Exponent σ // InBox H e} ≃ Fin (2 * H + 1) × (σ → Fin (H + 1)) where
  toFun x :=
    (⟨(x.1 none + H).toNat, by have := x.2.1.2; omega⟩,
     fun i => ⟨(x.1 (some i)).toNat, by have := (x.2.2 i).2; omega⟩)
  invFun y := ⟨fun i => match i with
    | none => (y.1.val : ℤ) - H
    | some k => (y.2 k).val, by
      constructor
      · have := y.1.isLt
        change - (H : ℤ) ≤ (y.1.val : ℤ) - H ∧ (y.1.val : ℤ) - H ≤ H
        omega
      · intro i
        have := (y.2 i).isLt
        change 0 ≤ ((y.2 i).val : ℤ) ∧ ((y.2 i).val : ℤ) ≤ H
        omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      change ((x.1 none + H).toNat : ℤ) - H = x.1 none
      have := x.2.1.1
      omega
    | some k =>
      change ((x.1 (some k)).toNat : ℤ) = x.1 (some k)
      exact Int.toNat_of_nonneg (x.2.2 k).1
  right_inv y := by
    apply Prod.ext
    · apply Fin.ext
      change (((y.1.val : ℤ) - H + H).toNat) = y.1.val
      simp
    · funext i
      apply Fin.ext
      exact Int.toNat_natCast _

/-- Finiteness of the actual subtype of box monomials used as row and column indices. -/
noncomputable instance boxFintype [Fintype σ] (H : ℕ) :
    Fintype {e : Exponent σ // InBox H e} := by
  classical
  exact Fintype.ofEquiv _ (boxEquiv H).symm

/-- The number of Laurent monomial tests in the residue pin vector. -/
theorem box_card [Fintype σ] (H : ℕ) :
    Fintype.card {e : Exponent σ // InBox H e} =
      (2 * H + 1) * (H + 1) ^ Fintype.card σ := by
  classical
  rw [Fintype.card_congr (boxEquiv H), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

end ResidueBox

end BorderVNP
end Computability
end OAI
