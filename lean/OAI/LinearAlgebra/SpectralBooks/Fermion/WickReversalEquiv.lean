import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversal

/-! # Reversing a partial Wick matching twice -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

variable {α : Type*}

@[simp] theorem reverse_skipCol (x : α) (l r : List α) (p : Matching l r) :
    reverse (skipCol x p) = (.inl (reverse p) : Matching (x :: r) l) := by
  induction l generalizing r with
  | nil => rfl
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [skipCol, reverse, ih]
      rfl
    · exact (congrArg (pairAt (l := x :: r) (r := l) y j.succ) (ih _ p)).trans rfl

@[simp] theorem reverse_pairAt (x : α) (l r : List α) (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    reverse (pairAt x j p) = (.inr ⟨j, reverse p⟩ : Matching (x :: r) l) := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero => rfl
    | succ j =>
      change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩
      · simp only [pairAt, reverse, skipCol, ih]
        rfl
      · exact (congrArg (pairAt (l := x :: r) (r := l) y k.succ)
          (ih _ ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p)).trans rfl

@[simp] theorem reverse_reverse (l r : List α) (p : Matching l r) : reverse (reverse p) = p := by
  induction l generalizing r with
  | nil => exact Subsingleton.elim (α := Unit) _ _
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, reverse_skipCol, ih]
      rfl
    · simp only [reverse, reverse_pairAt, ih]
      rfl

/-- Interchanging blocks induces a bijection on all partial Wick matchings. -/
def reverseEquiv (l r : List α) : Matching l r ≃ Matching r l where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse l r
  right_inv := reverse_reverse r l

end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
