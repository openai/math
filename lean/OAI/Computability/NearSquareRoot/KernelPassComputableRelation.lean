import OAI.Computability.NearSquareRoot.KernelPassComputableSyntax
import Mathlib.Data.List.Forall2

/-! # Relational correctness of the numerical prefix interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

variable {σ τ : Type*}

private theorem getD_rel {R : σ → τ → Prop} {s : List σ} {t : List τ}
    (hs : List.Forall₂ R s t) {u : σ} {v : τ} (hd : R u v) (n : ℕ) :
    R (s.getD n u) (t.getD n v) := by
  induction hs generalizing n with
  | nil => simpa [List.getD] using hd
  | cons ha _ ih =>
    cases n with
    | zero => exact ha
    | succ n => exact ih n

theorem Algebra.parse_rel {a : Algebra σ} {b : Algebra τ} (R : σ → τ → Prop)
    (h₀ : R a.empty b.empty) (h₁ : ∀ op, R (a.leaf op) (b.leaf op))
    (h₂ : ∀ p q s t, R p s → R q t → R (a.seq p q) (b.seq s t))
    (h₃ : ∀ p q s t, R p s → R q t → R (a.parallel p q) (b.parallel s t))
    (ops : List Op) : R (a.parse ops) (b.parse ops) := by
  have hl : List.Forall₂ R (ops.foldr a.step []) (ops.foldr b.step []) := by
    induction ops with
    | nil => exact .nil
    | cons op ops ih =>
      simp only [List.foldr_cons, Algebra.step]
      split_ifs
      · exact .cons (h₂ _ _ _ _ (getD_rel ih h₀ 0) (getD_rel ih h₀ 1)) (List.forall₂_drop 2 ih)
      · exact .cons (h₃ _ _ _ _ (getD_rel ih h₀ 0) (getD_rel ih h₀ 1)) (List.forall₂_drop 2 ih)
      · exact .cons (h₁ op) ih
  exact getD_rel hl h₀ 0

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
