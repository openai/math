import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversal

/-! # Ordered unmatched fields under exchange of the two Wick blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

variable {α : Type*}

/-- The fields of the left word that survive the contractions, in their original order. -/
def leftRest : {l r : List α} → Matching l r → List α
  | [], _, _ => []
  | x :: _, _, .inl p => x :: leftRest p
  | _ :: _, _, .inr ⟨_,p⟩ => leftRest p

/-- The fields of the right word that survive the contractions, in their original order. -/
def rightRest : {l r : List α} → Matching l r → List α
  | [], r, _ => r
  | _ :: _, _, .inl p => rightRest p
  | _ :: _, _, .inr ⟨_,p⟩ => rightRest p

theorem residual_eq_append {l r : List α} (p : Matching l r) :
    p.residual = p.leftRest ++ p.rightRest := by
  induction l generalizing r with
  | nil => rfl
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [residual, leftRest, rightRest, ih]

private theorem rest_skipCol (x : α) {l r : List α} (p : Matching l r) :
    (skipCol x p).leftRest = p.leftRest ∧ (skipCol x p).rightRest = x :: p.rightRest := by
  induction l generalizing r with
  | nil => exact ⟨rfl,rfl⟩
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [skipCol, leftRest, rightRest, (ih p).1, (ih p).2]

private theorem rest_pairAt (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    (pairAt x j p).leftRest = p.leftRest ∧ (pairAt x j p).rightRest = p.rightRest := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · exact ⟨rfl,rfl⟩
    · change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩ <;>
        simpa [pairAt, leftRest, rightRest] using ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p

private theorem rest_noCols (l : List α) :
    (noCols l).leftRest = l ∧ (noCols l).rightRest = [] := by
  induction l with
  | nil => exact ⟨rfl,rfl⟩
  | cons x l ih => simp [noCols, leftRest, rightRest, ih]

private theorem rest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.leftRest = p.rightRest ∧ p.reverse.rightRest = p.leftRest := by
  induction l generalizing r with
  | nil => exact rest_noCols r
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, leftRest, rightRest, (rest_skipCol x p.reverse).1,
        (rest_skipCol x p.reverse).2, (ih p).1, (ih p).2, and_self]
    · simpa only [reverse, leftRest, rightRest, (rest_pairAt x j p.reverse).1,
        (rest_pairAt x j p.reverse).2] using ih p

/-- Exchanging the two blocks preserves the unmatched right fields as the new left word. -/
@[simp] theorem leftRest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.leftRest = p.rightRest := (rest_reverse p).1

/-- Exchanging the two blocks preserves the unmatched left fields as the new right word. -/
@[simp] theorem rightRest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.rightRest = p.leftRest := (rest_reverse p).2

end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
